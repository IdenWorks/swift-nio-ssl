//===----------------------------------------------------------------------===//
//
// This source file is part of the SwiftNIO open source project
//
// Copyright (c) 2026 Apple Inc. and the SwiftNIO project authors
// Licensed under Apache License v2.0
//
// See LICENSE.txt for license information
// See CONTRIBUTORS.txt for the list of SwiftNIO project authors
//
// SPDX-License-Identifier: Apache-2.0
//
//===----------------------------------------------------------------------===//

@_implementationOnly import CNIOBoringSSL
import NIOConcurrencyHelpers
import NIOCore
import NIOEmbedded
import XCTest

@testable import NIOSSL

/// Records what a client's TLS handler passes on, in order. A reader such as
/// NIOAsyncChannel stops at the first error or close, so order matters.
private final class ReadRecorder: ChannelInboundHandler {
    typealias InboundIn = ByteBuffer

    var received = ByteBuffer()
    var errors: [Error] = []
    /// "data", "inputClosed", "inactive" or "error".
    var events: [String] = []

    func channelRead(context: ChannelHandlerContext, data: NIOAny) {
        var bytes = self.unwrapInboundIn(data)
        self.received.writeBuffer(&bytes)
        self.events.append("data")
    }

    func userInboundEventTriggered(context: ChannelHandlerContext, event: Any) {
        if let event = event as? ChannelEvent, event == .inputClosed {
            self.events.append("inputClosed")
        }
        context.fireUserInboundEventTriggered(event)
    }

    func channelInactive(context: ChannelHandlerContext) {
        self.events.append("inactive")
        context.fireChannelInactive()
    }

    func errorCaught(context: ChannelHandlerContext, error: Error) {
        self.errors.append(error)
        self.events.append("error")
    }
}

/// A server driven through BoringSSL's API directly, over memory BIOs, because a
/// NIOSSLHandler cannot send a fatal close_notify.
private final class RawBoringSSLServer {
    private let context: OpaquePointer
    private let ssl: OpaquePointer
    private let fromClient: UnsafeMutablePointer<BIO>
    private let toClient: UnsafeMutablePointer<BIO>

    init(certificate: NIOSSLCertificate, key: NIOSSLPrivateKey) {
        let context = CNIOBoringSSL_SSL_CTX_new(CNIOBoringSSL_TLS_method())!
        // No session tickets, so the server's first application record has
        // sequence number zero.
        precondition(CNIOBoringSSL_SSL_CTX_set_num_tickets(context, 0) == 1)
        certificate.withUnsafeMutableX509Pointer { x509 in
            precondition(CNIOBoringSSL_SSL_CTX_use_certificate(context, x509) == 1)
        }
        key.withUnsafeMutableEVPPKEYPointer { pkey in
            precondition(CNIOBoringSSL_SSL_CTX_use_PrivateKey(context, pkey) == 1)
        }
        self.context = context
        self.ssl = CNIOBoringSSL_SSL_new(context)!
        self.fromClient = CNIOBoringSSL_BIO_new(CNIOBoringSSL_BIO_s_mem())!
        self.toClient = CNIOBoringSSL_BIO_new(CNIOBoringSSL_BIO_s_mem())!
        // The SSL object takes ownership of both BIOs.
        CNIOBoringSSL_SSL_set_bio(self.ssl, self.fromClient, self.toClient)
        CNIOBoringSSL_SSL_set_accept_state(self.ssl)
    }

    deinit {
        CNIOBoringSSL_SSL_free(self.ssl)
        CNIOBoringSSL_SSL_CTX_free(self.context)
    }

    var protocolVersion: CInt {
        CNIOBoringSSL_SSL_version(self.ssl)
    }

    var isHandshakeDone: Bool {
        CNIOBoringSSL_SSL_is_init_finished(self.ssl) == 1
    }

    var cipherSuite: UInt16 {
        CNIOBoringSSL_SSL_CIPHER_get_protocol_id(CNIOBoringSSL_SSL_get_current_cipher(self.ssl))
    }

    /// Takes the client's bytes and advances the handshake.
    func receive(_ bytes: ByteBuffer) {
        bytes.withUnsafeReadableBytes { pointer in
            _ = CNIOBoringSSL_BIO_write(self.fromClient, pointer.baseAddress, CInt(pointer.count))
        }
        _ = CNIOBoringSSL_SSL_do_handshake(self.ssl)
    }

    func write(_ text: String) {
        let written = text.withCString { pointer in
            CNIOBoringSSL_SSL_write(self.ssl, pointer, CInt(text.utf8.count))
        }
        precondition(written == text.utf8.count)
    }

    /// Everything the server has written since the last call, as one buffer.
    func takeOutput() -> ByteBuffer {
        var output = ByteBuffer()
        var chunk = [UInt8](repeating: 0, count: 16384)
        while true {
            let count = CNIOBoringSSL_BIO_read(self.toClient, &chunk, CInt(chunk.count))
            if count <= 0 {
                return output
            }
            output.writeBytes(chunk[0..<Int(count)])
        }
    }
}

/// BoringSSL will not send close_notify at level fatal (`SSL_send_fatal_alert`
/// asserts against it), so this seals a fatal alert as a TLS 1.3 record itself,
/// with the server's application traffic secret.
private func sealedFatalAlert(
    description: UInt8,
    serverTrafficSecret: [UInt8],
    cipherSuite: UInt16,
    sequenceNumber: UInt64
) -> ByteBuffer {
    let aead: OpaquePointer
    let digest: OpaquePointer
    let keyLength: Int
    switch cipherSuite {
    case 0x1301:
        (aead, digest, keyLength) = (CNIOBoringSSL_EVP_aead_aes_128_gcm(), CNIOBoringSSL_EVP_sha256(), 16)
    case 0x1302:
        (aead, digest, keyLength) = (CNIOBoringSSL_EVP_aead_aes_256_gcm(), CNIOBoringSSL_EVP_sha384(), 32)
    case 0x1303:
        (aead, digest, keyLength) = (CNIOBoringSSL_EVP_aead_chacha20_poly1305(), CNIOBoringSSL_EVP_sha256(), 32)
    default:
        preconditionFailure("unexpected TLS 1.3 cipher suite \(cipherSuite)")
    }
    let key = expandLabel(serverTrafficSecret, label: "key", length: keyLength, digest: digest)
    let iv = expandLabel(serverTrafficSecret, label: "iv", length: 12, digest: digest)
    var nonce = iv
    for index in 0..<8 {
        nonce[11 - index] ^= UInt8(truncatingIfNeeded: sequenceNumber >> (8 * UInt64(index)))
    }
    // The alert, then its content type (alert, 21), per RFC 8446 section 5.2.
    let innerPlaintext: [UInt8] = [UInt8(SSL3_AL_FATAL), description, 21]
    let tagLength = Int(CNIOBoringSSL_EVP_AEAD_max_overhead(aead))
    let recordLength = innerPlaintext.count + tagLength
    let header: [UInt8] = [23, 3, 3, UInt8(recordLength >> 8), UInt8(recordLength & 0xff)]
    let context = CNIOBoringSSL_EVP_AEAD_CTX_new(aead, key, key.count, Int(EVP_AEAD_DEFAULT_TAG_LENGTH))!
    defer { CNIOBoringSSL_EVP_AEAD_CTX_free(context) }
    var sealed = [UInt8](repeating: 0, count: recordLength)
    var sealedLength = 0
    let result = CNIOBoringSSL_EVP_AEAD_CTX_seal(
        context, &sealed, &sealedLength, sealed.count, nonce, nonce.count,
        innerPlaintext, innerPlaintext.count, header, header.count
    )
    precondition(result == 1 && sealedLength == recordLength)
    var record = ByteBuffer()
    record.writeBytes(header)
    record.writeBytes(sealed)
    return record
}

/// HKDF-Expand-Label from RFC 8446 section 7.1, with an empty context.
private func expandLabel(_ secret: [UInt8], label: String, length: Int, digest: OpaquePointer) -> [UInt8] {
    let fullLabel = Array("tls13 \(label)".utf8)
    let info: [UInt8] = [UInt8(length >> 8), UInt8(length & 0xff), UInt8(fullLabel.count)] + fullLabel + [0]
    var output = [UInt8](repeating: 0, count: length)
    let result = CNIOBoringSSL_HKDF_expand(&output, length, digest, secret, secret.count, info, info.count)
    precondition(result == 1)
    return output
}

/// The SERVER_TRAFFIC_SECRET_0 line of an NSS key log.
private func serverTrafficSecret(in keyLog: [String]) -> [UInt8] {
    for line in keyLog {
        let fields = line.split(separator: " ")
        if fields.count == 3 && fields[0] == "SERVER_TRAFFIC_SECRET_0" {
            var bytes: [UInt8] = []
            var hex = Substring(fields[2])
            while !hex.isEmpty {
                bytes.append(UInt8(hex.prefix(2), radix: 16)!)
                hex = hex.dropFirst(2)
            }
            return bytes
        }
    }
    preconditionFailure("no SERVER_TRAFFIC_SECRET_0 in the key log")
}

final class FatalCloseNotifyTests: XCTestCase {
    // RFC 8446 section 6 lets TLS 1.3 peers ignore an alert's level, and some
    // servers send close_notify at level fatal. The bytes sent before it must
    // reach the reader before the connection closes, with no error.
    func testFatalLevelCloseNotifyDeliversTheDataThenCloses() throws {
        let recorder = try self.receiveFinalBytesThenFatalAlert(
            description: UInt8(SSL_AD_CLOSE_NOTIFY),
            allowRemoteHalfClosure: false
        )
        XCTAssertEqual(String(buffer: recorder.received), "final bytes")
        XCTAssertEqual(recorder.events, ["data", "inactive"], "\(recorder.errors)")
    }

    // With half-closure, the same alert ends only the input.
    func testFatalLevelCloseNotifyWithHalfClosureDeliversTheDataThenEndsInput() throws {
        let recorder = try self.receiveFinalBytesThenFatalAlert(
            description: UInt8(SSL_AD_CLOSE_NOTIFY),
            allowRemoteHalfClosure: true
        )
        XCTAssertEqual(String(buffer: recorder.received), "final bytes")
        XCTAssertEqual(recorder.events, ["data", "inputClosed"], "\(recorder.errors)")
    }

    // Only close_notify changed: any other fatal alert still fails the read.
    func testOtherFatalAlertsStillFail() throws {
        let recorder = try self.receiveFinalBytesThenFatalAlert(
            description: UInt8(SSL_AD_INTERNAL_ERROR),
            allowRemoteHalfClosure: false
        )
        XCTAssertTrue(recorder.events.contains("error"), "\(recorder.events)")
        XCTAssertTrue("\(recorder.errors)".contains("TLSV1_ALERT_INTERNAL_ERROR"), "\(recorder.errors)")
    }

    /// Completes a TLS 1.3 handshake between a raw BoringSSL server and an NIOSSL
    /// client, then delivers "final bytes" and a fatal alert in one read, as a
    /// real server's last packet would arrive.
    private func receiveFinalBytesThenFatalAlert(
        description: UInt8,
        allowRemoteHalfClosure: Bool
    ) throws -> ReadRecorder {
        let (certificate, key) = generateSelfSignedCert()
        let server = RawBoringSSLServer(certificate: certificate, key: key)
        var configuration = TLSConfiguration.makeClientConfiguration()
        configuration.certificateVerification = .noHostnameVerification
        configuration.trustRoots = .certificates([certificate])
        let keyLog = NIOLockedValueBox<[String]>([])
        configuration.keyLogCallback = { line in
            keyLog.withLockedValue { lines in
                lines.append(String(buffer: line).trimmingCharacters(in: .whitespacesAndNewlines))
            }
        }
        let clientContext = try NIOSSLContext(configuration: configuration)
        let client = EmbeddedChannel()
        client.allowRemoteHalfClosure = allowRemoteHalfClosure
        let recorder = ReadRecorder()
        try client.pipeline.syncOperations.addHandler(
            try NIOSSLClientHandler(context: clientContext, serverHostname: nil)
        )
        try client.pipeline.syncOperations.addHandler(recorder)
        _ = try client.connect(to: SocketAddress(ipAddress: "127.0.0.1", port: 443)).wait()

        for _ in 0..<4 {
            client.embeddedEventLoop.run()
            while let bytes = try client.readOutbound(as: ByteBuffer.self) {
                server.receive(bytes)
            }
            let reply = server.takeOutput()
            if reply.readableBytes > 0 {
                try client.writeInbound(reply)
                client.pipeline.fireChannelReadComplete()
            }
        }
        XCTAssertTrue(server.isHandshakeDone)
        XCTAssertEqual(server.protocolVersion, TLS1_3_VERSION)

        server.write("final bytes")
        var finalRead = server.takeOutput()
        var alert = sealedFatalAlert(
            description: description,
            serverTrafficSecret: serverTrafficSecret(in: keyLog.withLockedValue { lines in lines }),
            cipherSuite: server.cipherSuite,
            sequenceNumber: 1
        )
        finalRead.writeBuffer(&alert)
        try client.writeInbound(finalRead)
        client.pipeline.fireChannelReadComplete()
        return recorder
    }
}
