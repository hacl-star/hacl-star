module Spec.HPKE.Test

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module HPKE = Spec.Agile.HPKE
module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF

friend Spec.Agile.HPKE

// Test1: A.1, DHKEM(Curve25519), HKDF-SHA256, AES-GCM-128
// Base Setup
// mode: 0
// kemID: 2
// kdfID: 1
// aeadID: 1
// info: 4f6465206f6e2061204772656369616e2055726e
// skR: 39516b2f05e9757e21331c6f2019045f52cee01a741e2a8b50380408d0717fd9
// skS: eea949550bb218c921ab85cbc5003f4ef6257db1b47b7ed63a223c8360ef81e3
// skE: a1f7746c45d1a0eb72b996e0e7ecddba0e60a583a5e143796981101a3aaf8966
// psk: 3564623362383061383163623633636135393437306338333431346566373061633
// 1636338303636333964303133353738343937343061303364616464666339
// pskID: 456e6e796e20447572696e206172616e204d6f726961
// pkR: 14fdb807c79fb787d47890d502bce7c335d0809a053b9287e30fc608fcfc9d26
// pkS: 6eac89bc5d63e7b40c394a4218b6a8203803749f95fca2369611ed41afb97e06
// pkE: 0454a5a10ecaf982219eae4b5c36bc3e1606813caae1d262528396c60de44e3d
// enc: 0454a5a10ecaf982219eae4b5c36bc3e1606813caae1d262528396c60de44e3d
// zz: 15178ef77262b0468ee828a6da4f2620434a9edfdddfe9256ac53f8c6b7e575d
// context: 000002000100010454a5a10ecaf982219eae4b5c36bc3e1606813caae1d2625
// 28396c60de44e3d14fdb807c79fb787d47890d502bce7c335d0809a053b9287e30fc608f
// cfc9d260000000000000000000000000000000000000000000000000000000000000000e
// 3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b85555c404062
// 9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
// secret: c5fdbbad5c72ed703581bbcd3fe890a7ed46d6bf00c73c9755bffbcd6744f22b
// key: 11cf34f93b3d1e8f2e36f91c5a2d6818
// nonce: 23acef669d7f3bcc98f6d0ab

// sequence number: 0
// plaintext: 4265617574792069732074727574682c20747275746820626561757479
// aad: 436f756e742d30
// nonce: 23acef669d7f3bcc98f6d0ab
// ciphertext: 13fc68aef8e2c4591a0dd92c01ffe9573314d881cf71dd5708644ee71848
// 18e457de3b4d51eb1deb4f0beb35d1

// sequence number: 1
// plaintext: 4265617574792069732074727574682c20747275746820626561757479
// aad: 436f756e742d31
// nonce: 23acef669d7f3bcc98f6d0aa
// ciphertext: 2d7f0e514ce14abf93b0fcc34347e20d23008465c6f98aedc1f1fa806bfc
// 07708ff20ae9989bb770b18493f3af

// sequence number: 2
// plaintext: 4265617574792069732074727574682c20747275746820626561757479
// aad: 436f756e742d32
// nonce: 23acef669d7f3bcc98f6d0a9
// ciphertext: 3fa07d648ba64a5dd3816c2a512937c2a58b8428a1067b5ac15841541d5c
// 6d28cd415faba7d552d606d6c5f48c

// sequence number: 4
// plaintext: 4265617574792069732074727574682c20747275746820626561757479
// aad: 436f756e742d34
// nonce: 23acef669d7f3bcc98f6d0af
// ciphertext: 3aeeea18f990589141df055a90f382a8096dbdae8f912291cfeff475ede4
// f9b023c3ce88f499f5a2dc44454241

let test1_ciphersuite = DH.DH_Curve25519, AEAD.AES128_GCM, Hash.SHA2_256

let test1_info = List.Tot.map u8_from_UInt8 [
  0x4fuy; 0x64uy; 0x65uy; 0x20uy; 0x6fuy;
  0x6euy; 0x20uy; 0x61uy; 0x20uy; 0x47uy;
  0x72uy; 0x65uy; 0x63uy; 0x69uy; 0x61uy;
  0x6euy; 0x20uy; 0x55uy; 0x72uy; 0x6euy
]

let test1_skR = List.Tot.map u8_from_UInt8 [
  0x39uy; 0x51uy; 0x6buy; 0x2fuy; 0x05uy;
  0xe9uy; 0x75uy; 0x7euy; 0x21uy; 0x33uy;
  0x1cuy; 0x6fuy; 0x20uy; 0x19uy; 0x04uy;
  0x5fuy; 0x52uy; 0xceuy; 0xe0uy; 0x1auy;
  0x74uy; 0x1euy; 0x2auy; 0x8buy; 0x50uy;
  0x38uy; 0x04uy; 0x08uy; 0xd0uy; 0x71uy;
  0x7fuy; 0xd9uy;
]

let test1_skI = List.Tot.map u8_from_UInt8 [
  0xeeuy; 0xa9uy; 0x49uy; 0x55uy; 0x0buy;
  0xb2uy; 0x18uy; 0xc9uy; 0x21uy; 0xabuy;
  0x85uy; 0xcbuy; 0xc5uy; 0x00uy; 0x3fuy;
  0x4euy; 0xf6uy; 0x25uy; 0x7duy; 0xb1uy;
  0xb4uy; 0x7buy; 0x7euy; 0xd6uy; 0x3auy;
  0x22uy; 0x3cuy; 0x83uy; 0x60uy; 0xefuy;
  0x81uy; 0xe3uy;
]

let test1_skE = List.Tot.map u8_from_UInt8 [
  0xa1uy; 0xf7uy; 0x74uy; 0x6cuy; 0x45uy;
  0xd1uy; 0xa0uy; 0xebuy; 0x72uy; 0xb9uy;
  0x96uy; 0xe0uy; 0xe7uy; 0xecuy; 0xdduy;
  0xbauy; 0x0euy; 0x60uy; 0xa5uy; 0x83uy;
  0xa5uy; 0xe1uy; 0x43uy; 0x79uy; 0x69uy;
  0x81uy; 0x10uy; 0x1auy; 0x3auy; 0xafuy;
  0x89uy; 0x66uy;
]

let test1_psk = List.Tot.map u8_from_UInt8 [
  0x35uy; 0x64uy; 0x62uy; 0x33uy; 0x62uy;
  0x38uy; 0x30uy; 0x61uy; 0x38uy; 0x31uy;
  0x63uy; 0x62uy; 0x36uy; 0x33uy; 0x63uy;
  0x61uy; 0x35uy; 0x39uy; 0x34uy; 0x37uy;
  0x30uy; 0x63uy; 0x38uy; 0x33uy; 0x34uy;
  0x31uy; 0x34uy; 0x65uy; 0x66uy; 0x37uy;
  0x30uy; 0x61uy; 0x63uy; 0x31uy; 0x63uy;
  0x63uy; 0x38uy; 0x30uy; 0x36uy; 0x36uy;
  0x33uy; 0x39uy; 0x64uy; 0x30uy; 0x31uy;
  0x33uy; 0x35uy; 0x37uy; 0x38uy; 0x34uy;
  0x39uy; 0x37uy; 0x34uy; 0x30uy; 0x61uy;
  0x30uy; 0x33uy; 0x64uy; 0x61uy; 0x64uy;
  0x64uy; 0x66uy; 0x63uy; 0x39uy;
]


let test1_pskID = List.Tot.map u8_from_UInt8 [
  0x45uy; 0x6euy; 0x6euy; 0x79uy; 0x6euy;
  0x20uy; 0x44uy; 0x75uy; 0x72uy; 0x69uy;
  0x6euy; 0x20uy; 0x61uy; 0x72uy; 0x61uy;
  0x6euy; 0x20uy; 0x4duy; 0x6fuy; 0x72uy;
  0x69uy; 0x61uy
]

let test1_pkR = List.Tot.map u8_from_UInt8 [
  0x14uy; 0xfduy; 0xb8uy; 0x07uy; 0xc7uy;
  0x9fuy; 0xb7uy; 0x87uy; 0xd4uy; 0x78uy;
  0x90uy; 0xd5uy; 0x02uy; 0xbcuy; 0xe7uy;
  0xc3uy; 0x35uy; 0xd0uy; 0x80uy; 0x9auy;
  0x05uy; 0x3buy; 0x92uy; 0x87uy; 0xe3uy;
  0x0fuy; 0xc6uy; 0x08uy; 0xfcuy; 0xfcuy;
  0x9duy; 0x26uy;
]

let test1_pkI = List.Tot.map u8_from_UInt8 [
  0x6euy; 0xacuy; 0x89uy; 0xbcuy; 0x5duy;
  0x63uy; 0xe7uy; 0xb4uy; 0x0cuy; 0x39uy;
  0x4auy; 0x42uy; 0x18uy; 0xb6uy; 0xa8uy;
  0x20uy; 0x38uy; 0x03uy; 0x74uy; 0x9fuy;
  0x95uy; 0xfcuy; 0xa2uy; 0x36uy; 0x96uy;
  0x11uy; 0xeduy; 0x41uy; 0xafuy; 0xb9uy;
  0x7euy; 0x06uy;
]

let test1_pkE = List.Tot.map u8_from_UInt8 [
  0x04uy; 0x54uy; 0xa5uy; 0xa1uy; 0x0euy;
  0xcauy; 0xf9uy; 0x82uy; 0x21uy; 0x9euy;
  0xaeuy; 0x4buy; 0x5cuy; 0x36uy; 0xbcuy;
  0x3euy; 0x16uy; 0x06uy; 0x81uy; 0x3cuy;
  0xaauy; 0xe1uy; 0xd2uy; 0x62uy; 0x52uy;
  0x83uy; 0x96uy; 0xc6uy; 0x0duy; 0xe4uy;
  0x4euy; 0x3duy;
]

let test1_enc = List.Tot.map u8_from_UInt8 [
  0x04uy; 0x54uy; 0xa5uy; 0xa1uy; 0x0euy;
  0xcauy; 0xf9uy; 0x82uy; 0x21uy; 0x9euy;
  0xaeuy; 0x4buy; 0x5cuy; 0x36uy; 0xbcuy;
  0x3euy; 0x16uy; 0x06uy; 0x81uy; 0x3cuy;
  0xaauy; 0xe1uy; 0xd2uy; 0x62uy; 0x52uy;
  0x83uy; 0x96uy; 0xc6uy; 0x0duy; 0xe4uy;
  0x4euy; 0x3duy;
]

let test1_zz = List.Tot.map u8_from_UInt8 [
  0x15uy; 0x17uy; 0x8euy; 0xf7uy; 0x72uy;
  0x62uy; 0xb0uy; 0x46uy; 0x8euy; 0xe8uy;
  0x28uy; 0xa6uy; 0xdauy; 0x4fuy; 0x26uy;
  0x20uy; 0x43uy; 0x4auy; 0x9euy; 0xdfuy;
  0xdduy; 0xdfuy; 0xe9uy; 0x25uy; 0x6auy;
  0xc5uy; 0x3fuy; 0x8cuy; 0x6buy; 0x7euy;
  0x57uy; 0x5duy;
]

let test1_context = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x00uy; 0x02uy; 0x00uy; 0x01uy;
  0x00uy; 0x01uy; 0x04uy; 0x54uy; 0xa5uy;
  0xa1uy; 0x0euy; 0xcauy; 0xf9uy; 0x82uy;
  0x21uy; 0x9euy; 0xaeuy; 0x4buy; 0x5cuy;
  0x36uy; 0xbcuy; 0x3euy; 0x16uy; 0x06uy;
  0x81uy; 0x3cuy; 0xaauy; 0xe1uy; 0xd2uy;
  0x62uy; 0x52uy; 0x83uy; 0x96uy; 0xc6uy;
  0x0duy; 0xe4uy; 0x4euy; 0x3duy; 0x14uy;
  0xfduy; 0xb8uy; 0x07uy; 0xc7uy; 0x9fuy;
  0xb7uy; 0x87uy; 0xd4uy; 0x78uy; 0x90uy;
  0xd5uy; 0x02uy; 0xbcuy; 0xe7uy; 0xc3uy;
  0x35uy; 0xd0uy; 0x80uy; 0x9auy; 0x05uy;
  0x3buy; 0x92uy; 0x87uy; 0xe3uy; 0x0fuy;
  0xc6uy; 0x08uy; 0xfcuy; 0xfcuy; 0x9duy;
  0x26uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0xe3uy; 0xb0uy;
  0xc4uy; 0x42uy; 0x98uy; 0xfcuy; 0x1cuy;
  0x14uy; 0x9auy; 0xfbuy; 0xf4uy; 0xc8uy;
  0x99uy; 0x6fuy; 0xb9uy; 0x24uy; 0x27uy;
  0xaeuy; 0x41uy; 0xe4uy; 0x64uy; 0x9buy;
  0x93uy; 0x4cuy; 0xa4uy; 0x95uy; 0x99uy;
  0x1buy; 0x78uy; 0x52uy; 0xb8uy; 0x55uy;
  0x55uy; 0xc4uy; 0x04uy; 0x06uy; 0x29uy;
  0xc6uy; 0x4cuy; 0x5euy; 0xfeuy; 0xc2uy;
  0xf7uy; 0x23uy; 0x04uy; 0x07uy; 0xd6uy;
  0x12uy; 0xd1uy; 0x62uy; 0x89uy; 0xd7uy;
  0xc5uy; 0xd7uy; 0xafuy; 0xcfuy; 0x93uy;
  0x40uy; 0x28uy; 0x0auy; 0xbduy; 0x2duy;
  0xe1uy; 0xabuy;
]

let test1_secret = List.Tot.map u8_from_UInt8 [
  0xc5uy; 0xfduy; 0xbbuy; 0xaduy; 0x5cuy;
  0x72uy; 0xeduy; 0x70uy; 0x35uy; 0x81uy;
  0xbbuy; 0xcduy; 0x3fuy; 0xe8uy; 0x90uy;
  0xa7uy; 0xeduy; 0x46uy; 0xd6uy; 0xbfuy;
  0x00uy; 0xc7uy; 0x3cuy; 0x97uy; 0x55uy;
  0xbfuy; 0xfbuy; 0xcduy; 0x67uy; 0x44uy;
  0xf2uy; 0x2buy;
]

let test1_key = List.Tot.map u8_from_UInt8 [
  0x11uy; 0xcfuy; 0x34uy; 0xf9uy; 0x3buy;
  0x3duy; 0x1euy; 0x8fuy; 0x2euy; 0x36uy;
  0xf9uy; 0x1cuy; 0x5auy; 0x2duy; 0x68uy;
  0x18uy;
]

let test1_nonce = List.Tot.map u8_from_UInt8 [
  0x23uy; 0xacuy; 0xefuy; 0x66uy; 0x9duy;
  0x7fuy; 0x3buy; 0xccuy; 0x98uy; 0xf6uy;
  0xd0uy; 0xabuy;
]

let test1_plaintext = List.Tot.map u8_from_UInt8 [
  0x42uy; 0x65uy; 0x61uy; 0x75uy; 0x74uy;
  0x79uy; 0x20uy; 0x69uy; 0x73uy; 0x20uy;
  0x74uy; 0x72uy; 0x75uy; 0x74uy; 0x68uy;
  0x2cuy; 0x20uy; 0x74uy; 0x72uy; 0x75uy;
  0x74uy; 0x68uy; 0x20uy; 0x62uy; 0x65uy;
  0x61uy; 0x75uy; 0x74uy; 0x79uy;
]

let test1_aad0 = List.Tot.map u8_from_UInt8 [
  0x43uy; 0x6fuy; 0x75uy; 0x6euy; 0x74uy;
  0x2duy; 0x30uy;
]

let test1_nonce0 = List.Tot.map u8_from_UInt8 [
  0x23uy; 0xacuy; 0xefuy; 0x66uy; 0x9duy;
  0x7fuy; 0x3buy; 0xccuy; 0x98uy; 0xf6uy;
  0xd0uy; 0xabuy;
]

let test1_cipher0 = List.Tot.map u8_from_UInt8 [
  0x13uy; 0xfcuy; 0x68uy; 0xaeuy; 0xf8uy;
  0xe2uy; 0xc4uy; 0x59uy; 0x1auy; 0x0duy;
  0xd9uy; 0x2cuy; 0x01uy; 0xffuy; 0xe9uy;
  0x57uy; 0x33uy; 0x14uy; 0xd8uy; 0x81uy;
  0xcfuy; 0x71uy; 0xdduy; 0x57uy; 0x08uy;
  0x64uy; 0x4euy; 0xe7uy; 0x18uy; 0x48uy;
  0x18uy; 0xe4uy; 0x57uy; 0xdeuy; 0x3buy;
  0x4duy; 0x51uy; 0xebuy; 0x1duy; 0xebuy;
  0x4fuy; 0x0buy; 0xebuy; 0x35uy; 0xd1uy;
]

// DHKEM(P-256), HKDF-SHA256, ChaCha20Poly1305
// Base Setup
// mode: 0
// kemID: 1
// kdfID: 1
// aeadID: 3
// info: 4f6465206f6e2061204772656369616e2055726e
// skR: efd90477fdb7b8f60357eec8d7ae348fef38b0c55c3298c09caf9d575990bd22
// skS: 2ee3b88417a20b5fb0a527fefaae4066a6449d2d75bed96fa2478d58f300c411
// skE: 2118dc1de1f6578b3576b4e6996fa6517ceb28a403fce626c8e0d430bd571f8b
// psk: 3564623362383061383163623633636135393437306338333431346566373061633
// 1636338303636333964303133353738343937343061303364616464666339
// pskID: 456e6e796e20447572696e206172616e204d6f726961
// pkR: 0441aa0ed8d749bab7f9a2ed9515ea60ad5b5cace45710f4ce6bf99bb44a1069d8a
// 9c12ef2f514fb1c9185c8db167c821b2aeb38d1f821ba1164101c85ede7ee13
// pkS: 047a9f60ef11a46a211fa3ca38c14430a282cefac5b90866918d64ffad2cdfe7d41
// fed52aaea83f703407ed9bb3db950023a1accb689ba91b5743cec9d4680d080
// pkE: 049904661176dd864002718fee7b491330d54f45bd37172b6b9ae8038cce88b9f9f
// ad47829699477de2fb014827b4a8e7f1e4a870304aad3d7986d68d35cd07ff6
// enc: 049904661176dd864002718fee7b491330d54f45bd37172b6b9ae8038cce88b9f9f
// ad47829699477de2fb014827b4a8e7f1e4a870304aad3d7986d68d35cd07ff6
// zz: cd6e7bb5ff8c134f2a925e9ca022e65f5b487321bc3e576f377e6f01236a1bbb
// context: 00000100010003049904661176dd864002718fee7b491330d54f45bd37172b6
// b9ae8038cce88b9f9fad47829699477de2fb014827b4a8e7f1e4a870304aad3d7986d68d
// 35cd07ff60441aa0ed8d749bab7f9a2ed9515ea60ad5b5cace45710f4ce6bf99bb44a106
// 9d8a9c12ef2f514fb1c9185c8db167c821b2aeb38d1f821ba1164101c85ede7ee1300000
// 000000000000000000000000000000000000000000000000000000000000000000000000
// 00000000000000000000000000000000000000000000000000000e3b0c44298fc1c149af
// bf4c8996fb92427ae41e4649b934ca495991b7852b85555c4040629c64c5efec2f723040
// 7d612d16289d7c5d7afcf9340280abd2de1ab
// secret: 15a36bf657d3b3b4eb355d6bf2a595f710e4a4da37d2710964167ba8029227ee
// key: fe8f6e7d61f81dc4cce9b185b4343323dcf7eaab8c2ac36239b2a9274c198868
// nonce: e61fbe136571b0fa5753e51d

let test2_ciphersuite = DH.DH_P256, AEAD.CHACHA20_POLY1305, Hash.SHA2_256

let test2_info = List.Tot.map u8_from_UInt8 [
  0x4fuy; 0x64uy; 0x65uy; 0x20uy; 0x6fuy;
  0x6euy; 0x20uy; 0x61uy; 0x20uy; 0x47uy;
  0x72uy; 0x65uy; 0x63uy; 0x69uy; 0x61uy;
  0x6euy; 0x20uy; 0x55uy; 0x72uy; 0x6euy;
]

let test2_skR = List.Tot.map u8_from_UInt8 [
  0xefuy; 0xd9uy; 0x04uy; 0x77uy; 0xfduy;
  0xb7uy; 0xb8uy; 0xf6uy; 0x03uy; 0x57uy;
  0xeeuy; 0xc8uy; 0xd7uy; 0xaeuy; 0x34uy;
  0x8fuy; 0xefuy; 0x38uy; 0xb0uy; 0xc5uy;
  0x5cuy; 0x32uy; 0x98uy; 0xc0uy; 0x9cuy;
  0xafuy; 0x9duy; 0x57uy; 0x59uy; 0x90uy;
  0xbduy; 0x22uy;
]

let test2_skI = List.Tot.map u8_from_UInt8 [
  0x2euy; 0xe3uy; 0xb8uy; 0x84uy; 0x17uy;
  0xa2uy; 0x0buy; 0x5fuy; 0xb0uy; 0xa5uy;
  0x27uy; 0xfeuy; 0xfauy; 0xaeuy; 0x40uy;
  0x66uy; 0xa6uy; 0x44uy; 0x9duy; 0x2duy;
  0x75uy; 0xbeuy; 0xd9uy; 0x6fuy; 0xa2uy;
  0x47uy; 0x8duy; 0x58uy; 0xf3uy; 0x00uy;
  0xc4uy; 0x11uy;
]

let test2_skE = List.Tot.map u8_from_UInt8 [
  0x21uy; 0x18uy; 0xdcuy; 0x1duy; 0xe1uy;
  0xf6uy; 0x57uy; 0x8buy; 0x35uy; 0x76uy;
  0xb4uy; 0xe6uy; 0x99uy; 0x6fuy; 0xa6uy;
  0x51uy; 0x7cuy; 0xebuy; 0x28uy; 0xa4uy;
  0x03uy; 0xfcuy; 0xe6uy; 0x26uy; 0xc8uy;
  0xe0uy; 0xd4uy; 0x30uy; 0xbduy; 0x57uy;
  0x1fuy; 0x8buy;
]

let test2_psk = List.Tot.map u8_from_UInt8 [
  0x35uy; 0x64uy; 0x62uy; 0x33uy; 0x62uy;
  0x38uy; 0x30uy; 0x61uy; 0x38uy; 0x31uy;
  0x63uy; 0x62uy; 0x36uy; 0x33uy; 0x63uy;
  0x61uy; 0x35uy; 0x39uy; 0x34uy; 0x37uy;
  0x30uy; 0x63uy; 0x38uy; 0x33uy; 0x34uy;
  0x31uy; 0x34uy; 0x65uy; 0x66uy; 0x37uy;
  0x30uy; 0x61uy; 0x63uy; 0x31uy; 0x63uy;
  0x63uy; 0x38uy; 0x30uy; 0x36uy; 0x36uy;
  0x33uy; 0x39uy; 0x64uy; 0x30uy; 0x31uy;
  0x33uy; 0x35uy; 0x37uy; 0x38uy; 0x34uy;
  0x39uy; 0x37uy; 0x34uy; 0x30uy; 0x61uy;
  0x30uy; 0x33uy; 0x64uy; 0x61uy; 0x64uy;
  0x64uy; 0x66uy; 0x63uy; 0x39uy;
]

let test2_pskID = List.Tot.map u8_from_UInt8 [
  0x45uy; 0x6euy; 0x6euy; 0x79uy; 0x6euy;
  0x20uy; 0x44uy; 0x75uy; 0x72uy; 0x69uy;
  0x6euy; 0x20uy; 0x61uy; 0x72uy; 0x61uy;
  0x6euy; 0x20uy; 0x4duy; 0x6fuy; 0x72uy;
  0x69uy; 0x61uy;
]

let test2_pkR = List.Tot.map u8_from_UInt8 [
  0x04uy; 0x41uy; 0xaauy; 0x0euy; 0xd8uy;
  0xd7uy; 0x49uy; 0xbauy; 0xb7uy; 0xf9uy;
  0xa2uy; 0xeduy; 0x95uy; 0x15uy; 0xeauy;
  0x60uy; 0xaduy; 0x5buy; 0x5cuy; 0xacuy;
  0xe4uy; 0x57uy; 0x10uy; 0xf4uy; 0xceuy;
  0x6buy; 0xf9uy; 0x9buy; 0xb4uy; 0x4auy;
  0x10uy; 0x69uy; 0xd8uy; 0xa9uy; 0xc1uy;
  0x2euy; 0xf2uy; 0xf5uy; 0x14uy; 0xfbuy;
  0x1cuy; 0x91uy; 0x85uy; 0xc8uy; 0xdbuy;
  0x16uy; 0x7cuy; 0x82uy; 0x1buy; 0x2auy;
  0xebuy; 0x38uy; 0xd1uy; 0xf8uy; 0x21uy;
  0xbauy; 0x11uy; 0x64uy; 0x10uy; 0x1cuy;
  0x85uy; 0xeduy; 0xe7uy; 0xeeuy; 0x13uy;
]

let test2_pkI = List.Tot.map u8_from_UInt8 [
  0x04uy; 0x7auy; 0x9fuy; 0x60uy; 0xefuy;
  0x11uy; 0xa4uy; 0x6auy; 0x21uy; 0x1fuy;
  0xa3uy; 0xcauy; 0x38uy; 0xc1uy; 0x44uy;
  0x30uy; 0xa2uy; 0x82uy; 0xceuy; 0xfauy;
  0xc5uy; 0xb9uy; 0x08uy; 0x66uy; 0x91uy;
  0x8duy; 0x64uy; 0xffuy; 0xaduy; 0x2cuy;
  0xdfuy; 0xe7uy; 0xd4uy; 0x1fuy; 0xeduy;
  0x52uy; 0xaauy; 0xeauy; 0x83uy; 0xf7uy;
  0x03uy; 0x40uy; 0x7euy; 0xd9uy; 0xbbuy;
  0x3duy; 0xb9uy; 0x50uy; 0x02uy; 0x3auy;
  0x1auy; 0xccuy; 0xb6uy; 0x89uy; 0xbauy;
  0x91uy; 0xb5uy; 0x74uy; 0x3cuy; 0xecuy;
  0x9duy; 0x46uy; 0x80uy; 0xd0uy; 0x80uy;
]

let test2_pkE = List.Tot.map u8_from_UInt8 [
  0x04uy; 0x99uy; 0x04uy; 0x66uy; 0x11uy;
  0x76uy; 0xdduy; 0x86uy; 0x40uy; 0x02uy;
  0x71uy; 0x8fuy; 0xeeuy; 0x7buy; 0x49uy;
  0x13uy; 0x30uy; 0xd5uy; 0x4fuy; 0x45uy;
  0xbduy; 0x37uy; 0x17uy; 0x2buy; 0x6buy;
  0x9auy; 0xe8uy; 0x03uy; 0x8cuy; 0xceuy;
  0x88uy; 0xb9uy; 0xf9uy; 0xfauy; 0xd4uy;
  0x78uy; 0x29uy; 0x69uy; 0x94uy; 0x77uy;
  0xdeuy; 0x2fuy; 0xb0uy; 0x14uy; 0x82uy;
  0x7buy; 0x4auy; 0x8euy; 0x7fuy; 0x1euy;
  0x4auy; 0x87uy; 0x03uy; 0x04uy; 0xaauy;
  0xd3uy; 0xd7uy; 0x98uy; 0x6duy; 0x68uy;
  0xd3uy; 0x5cuy; 0xd0uy; 0x7fuy; 0xf6uy;
]

let test2_enc = List.Tot.map u8_from_UInt8 [
  0x04uy; 0x99uy; 0x04uy; 0x66uy; 0x11uy;
  0x76uy; 0xdduy; 0x86uy; 0x40uy; 0x02uy;
  0x71uy; 0x8fuy; 0xeeuy; 0x7buy; 0x49uy;
  0x13uy; 0x30uy; 0xd5uy; 0x4fuy; 0x45uy;
  0xbduy; 0x37uy; 0x17uy; 0x2buy; 0x6buy;
  0x9auy; 0xe8uy; 0x03uy; 0x8cuy; 0xceuy;
  0x88uy; 0xb9uy; 0xf9uy; 0xfauy; 0xd4uy;
  0x78uy; 0x29uy; 0x69uy; 0x94uy; 0x77uy;
  0xdeuy; 0x2fuy; 0xb0uy; 0x14uy; 0x82uy;
  0x7buy; 0x4auy; 0x8euy; 0x7fuy; 0x1euy;
  0x4auy; 0x87uy; 0x03uy; 0x04uy; 0xaauy;
  0xd3uy; 0xd7uy; 0x98uy; 0x6duy; 0x68uy;
  0xd3uy; 0x5cuy; 0xd0uy; 0x7fuy; 0xf6uy;
]

let test2_zz = List.Tot.map u8_from_UInt8 [
  0xcduy; 0x6euy; 0x7buy; 0xb5uy; 0xffuy;
  0x8cuy; 0x13uy; 0x4fuy; 0x2auy; 0x92uy;
  0x5euy; 0x9cuy; 0xa0uy; 0x22uy; 0xe6uy;
  0x5fuy; 0x5buy; 0x48uy; 0x73uy; 0x21uy;
  0xbcuy; 0x3euy; 0x57uy; 0x6fuy; 0x37uy;
  0x7euy; 0x6fuy; 0x01uy; 0x23uy; 0x6auy;
  0x1buy; 0xbbuy;
]

let test2_context = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x00uy; 0x01uy; 0x00uy; 0x01uy;
  0x00uy; 0x03uy; 0x04uy; 0x99uy; 0x04uy;
  0x66uy; 0x11uy; 0x76uy; 0xdduy; 0x86uy;
  0x40uy; 0x02uy; 0x71uy; 0x8fuy; 0xeeuy;
  0x7buy; 0x49uy; 0x13uy; 0x30uy; 0xd5uy;
  0x4fuy; 0x45uy; 0xbduy; 0x37uy; 0x17uy;
  0x2buy; 0x6buy; 0x9auy; 0xe8uy; 0x03uy;
  0x8cuy; 0xceuy; 0x88uy; 0xb9uy; 0xf9uy;
  0xfauy; 0xd4uy; 0x78uy; 0x29uy; 0x69uy;
  0x94uy; 0x77uy; 0xdeuy; 0x2fuy; 0xb0uy;
  0x14uy; 0x82uy; 0x7buy; 0x4auy; 0x8euy;
  0x7fuy; 0x1euy; 0x4auy; 0x87uy; 0x03uy;
  0x04uy; 0xaauy; 0xd3uy; 0xd7uy; 0x98uy;
  0x6duy; 0x68uy; 0xd3uy; 0x5cuy; 0xd0uy;
  0x7fuy; 0xf6uy; 0x04uy; 0x41uy; 0xaauy;
  0x0euy; 0xd8uy; 0xd7uy; 0x49uy; 0xbauy;
  0xb7uy; 0xf9uy; 0xa2uy; 0xeduy; 0x95uy;
  0x15uy; 0xeauy; 0x60uy; 0xaduy; 0x5buy;
  0x5cuy; 0xacuy; 0xe4uy; 0x57uy; 0x10uy;
  0xf4uy; 0xceuy; 0x6buy; 0xf9uy; 0x9buy;
  0xb4uy; 0x4auy; 0x10uy; 0x69uy; 0xd8uy;
  0xa9uy; 0xc1uy; 0x2euy; 0xf2uy; 0xf5uy;
  0x14uy; 0xfbuy; 0x1cuy; 0x91uy; 0x85uy;
  0xc8uy; 0xdbuy; 0x16uy; 0x7cuy; 0x82uy;
  0x1buy; 0x2auy; 0xebuy; 0x38uy; 0xd1uy;
  0xf8uy; 0x21uy; 0xbauy; 0x11uy; 0x64uy;
  0x10uy; 0x1cuy; 0x85uy; 0xeduy; 0xe7uy;
  0xeeuy; 0x13uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0xe3uy; 0xb0uy; 0xc4uy;
  0x42uy; 0x98uy; 0xfcuy; 0x1cuy; 0x14uy;
  0x9auy; 0xfbuy; 0xf4uy; 0xc8uy; 0x99uy;
  0x6fuy; 0xb9uy; 0x24uy; 0x27uy; 0xaeuy;
  0x41uy; 0xe4uy; 0x64uy; 0x9buy; 0x93uy;
  0x4cuy; 0xa4uy; 0x95uy; 0x99uy; 0x1buy;
  0x78uy; 0x52uy; 0xb8uy; 0x55uy; 0x55uy;
  0xc4uy; 0x04uy; 0x06uy; 0x29uy; 0xc6uy;
  0x4cuy; 0x5euy; 0xfeuy; 0xc2uy; 0xf7uy;
  0x23uy; 0x04uy; 0x07uy; 0xd6uy; 0x12uy;
  0xd1uy; 0x62uy; 0x89uy; 0xd7uy; 0xc5uy;
  0xd7uy; 0xafuy; 0xcfuy; 0x93uy; 0x40uy;
  0x28uy; 0x0auy; 0xbduy; 0x2duy; 0xe1uy;
  0xabuy;
]

let test2_secret = List.Tot.map u8_from_UInt8 [
  0x15uy; 0xa3uy; 0x6buy; 0xf6uy; 0x57uy;
  0xd3uy; 0xb3uy; 0xb4uy; 0xebuy; 0x35uy;
  0x5duy; 0x6buy; 0xf2uy; 0xa5uy; 0x95uy;
  0xf7uy; 0x10uy; 0xe4uy; 0xa4uy; 0xdauy;
  0x37uy; 0xd2uy; 0x71uy; 0x09uy; 0x64uy;
  0x16uy; 0x7buy; 0xa8uy; 0x02uy; 0x92uy;
  0x27uy; 0xeeuy;
]

let test2_key = List.Tot.map u8_from_UInt8 [
  0xfeuy; 0x8fuy; 0x6euy; 0x7duy; 0x61uy;
  0xf8uy; 0x1duy; 0xc4uy; 0xccuy; 0xe9uy;
  0xb1uy; 0x85uy; 0xb4uy; 0x34uy; 0x33uy;
  0x23uy; 0xdcuy; 0xf7uy; 0xeauy; 0xabuy;
  0x8cuy; 0x2auy; 0xc3uy; 0x62uy; 0x39uy;
  0xb2uy; 0xa9uy; 0x27uy; 0x4cuy; 0x19uy;
  0x88uy; 0x68uy;
]

let test2_nonce = List.Tot.map u8_from_UInt8 [
  0xe6uy; 0x1fuy; 0xbeuy; 0x13uy; 0x65uy;
  0x71uy; 0xb0uy; 0xfauy; 0x57uy; 0x53uy;
  0xe5uy; 0x1duy;
]


#set-options "--ifuel 1"
let test_base_setup
  (cs:HPKE.ciphersuite)
  (info:list uint8{List.Tot.length info <= HPKE.max_info})
  (skR:list uint8{List.Tot.length skR == HPKE.size_dh_key cs})
  (skI:list uint8{List.Tot.length skI == HPKE.size_dh_key cs})
  (skE:list uint8{List.Tot.length skE == HPKE.size_dh_key cs})
  (psk:list uint8) // {List.Tot.length psk == HPKE.size_psk cs})
  (pskID:list uint8) //{List.Tot.length pskID <= HPKE.max_pskID})
  (pkR:list uint8{List.Tot.length pkR == HPKE.size_dh_public cs})
  (pkI:list uint8{List.Tot.length pkI == HPKE.size_dh_public cs})
  (pkE:list uint8{List.Tot.length pkE == HPKE.size_dh_public cs})
  (enc:list uint8)
  (zz:list uint8{List.Tot.length zz == HPKE.size_dh_public cs})
  (context:list uint8) //{List.Tot.length context == 7 + 3 * HPKE.size_dh_public cs + 2 * Hash.size_hash (HPKE.hash_of_cs cs)})
  (secret:list uint8)
  (key:list uint8{List.Tot.length key == HPKE.size_aead_key cs})
  (nonce:list uint8{List.Tot.length nonce == HPKE.size_aead_nonce cs})
= // IO.print_string "Test encap\n";
  // let encap = HPKE.encap cs (of_list skE) (of_list pkR) in
  // let res_encap =
  //   if None? encap then (
  //      IO.print_string "encap returned None\n"; false
  //   ) else (
  //     let (returned_zz, returned_pkE) = Some?.v encap in
  //     let r2_a = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
  //       (of_list pkE) returned_pkE in
  //     let r2_b = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
  //       (of_list zz) returned_zz in
  //     if not r2_a then (
  //       IO.print_string "\nExpected pkE :";
  //       List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) pkE;
  //       IO.print_string "\nComputed pkE :";
  //       List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_pkE);
  //       IO.print_string "\n");
  //     if not r2_b then (
  //       IO.print_string "\nExpected zz :";
  //       List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) zz;
  //       IO.print_string "\nComputed zz :";
  //       List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_zz);
  //       IO.print_string "\n");
  //     r2_a && r2_b
  //   )

  // in

  // IO.print_string "Test ks_derive\n";

  // let (psk, pskID) = (HPKE.default_psk cs, HPKE.default_pskId) in
  // let pkI = HPKE.default_pkI cs in
  // let pskID_hash = Hash.hash (HPKE.hash_of_cs cs) pskID in
  // let info_hash = Hash.hash (HPKE.hash_of_cs cs) (of_list info) in
  // let returned_context = HPKE.build_context HPKE.Base cs (of_list pkE) (of_list pkR) pkI pskID_hash info_hash in


  // IO.print_string "\nExpected context :";
  // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) context;
  // IO.print_string "\nComputed context :";
  // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_context);
  // IO.print_string "\n";

  // let returned_secret = HKDF.extract (HPKE.hash_of_cs cs) psk (of_list zz) in

  // IO.print_string "\nExpected secret :";
  // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) secret;
  // IO.print_string "\nComputed secret :";
  // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_secret);
  // IO.print_string "\n";


  // let info_key = Seq.append HPKE.label_key (of_list context) in
  // let info_nonce = Seq.append HPKE.label_nonce (of_list context) in
  // let keyIR = HKDF.expand (HPKE.hash_of_cs cs) returned_secret info_key (HPKE.size_aead_key cs) in
  // let nonceIR = HKDF.expand (HPKE.hash_of_cs cs) returned_secret info_nonce (HPKE.size_aead_nonce cs) in

  // IO.print_string "\nExpected key :";
  // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) key;
  // IO.print_string "\nComputed key :";
  // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list keyIR);
  // IO.print_string "\n";

  // IO.print_string "\nExpected nonce :";
  // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) nonce;
  // IO.print_string "\nComputed nonce :";
  // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list nonceIR);
  // IO.print_string "\n";



  // let k, n = HPKE.ks_derive cs HPKE.Base (of_list pkR) (of_list zz) (of_list pkE)
  //   (of_list info) None None in

  IO.print_string "Test setupBaseS\n";
  let setupBaseS = HPKE.setupBaseS cs (of_list skE) (of_list pkR) (of_list info) in
  let res_setupBaseS =
    if None? setupBaseS then (
      IO.print_string "setupBaseS returned None\n"; false
    ) else (
      let returned_pkE, returned_key, returned_nonce = Some?.v setupBaseS in
      let r2_a = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
        (of_list pkE) returned_pkE in
      let r2_b = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
        (of_list key) returned_key in
      let r2_c = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
        (of_list nonce) returned_nonce in
      if not r2_a then (
        IO.print_string "\nExpected pkE :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) pkE;
        IO.print_string "\nComputed pkE :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_pkE);
        IO.print_string "\n");
      if not r2_b then (
        IO.print_string "\nExpected key :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) key;
        IO.print_string "\nComputed key :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_key);
        IO.print_string "\n");
      if not r2_c then (
        IO.print_string "\nExpected nonce :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) nonce;
        IO.print_string "\nComputed nonce :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_nonce);
        IO.print_string "\n");

      r2_a && r2_b && r2_c
    )
  in

  if res_setupBaseS then IO.print_string "setupBaseS succeeded\n" else IO.print_string "setupBaseS failed\n";

  IO.print_string "Test setupBaseR\n";
  let setupBaseR = HPKE.setupBaseR cs (of_list pkE) (of_list skR) (of_list info) in
  let res_setupBaseR =
    if None? setupBaseR then (
      IO.print_string "setupBaseR returned None\n"; false
    ) else (
      let returned_key, returned_nonce = Some?.v setupBaseR in
      let r2_a = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
        (of_list key) returned_key in
      let r2_b = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
        (of_list nonce) returned_nonce in
      if not r2_a then (
        IO.print_string "\nExpected key :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) key;
        IO.print_string "\nComputed key :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_key);
        IO.print_string "\n");
      if not r2_b then (
        IO.print_string "\nExpected nonce :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) nonce;
        IO.print_string "\nComputed nonce :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_nonce);
        IO.print_string "\n");

      r2_a && r2_b
    )
  in

  if res_setupBaseR then IO.print_string "setupBaseR succeeded\n" else IO.print_string "setupBaseR failed\n";

  res_setupBaseS && res_setupBaseR

let test_encrytion (cs:HPKE.ciphersuite)
  (skE:list uint8{List.Tot.length skE == HPKE.size_dh_key cs})
  (skR:list uint8{List.Tot.length skR == HPKE.size_dh_key cs})
  (pkR:list uint8{List.Tot.length pkR == HPKE.size_dh_public cs})
  (pkE:list uint8{List.Tot.length pkE == HPKE.size_dh_public cs})
  (plain:list uint8{List.Tot.length plain <= HPKE.max_length cs})
  (aad:list uint8{List.Tot.length aad <= HPKE.max_info})
  (cipher:list uint8{
    List.Tot.length cipher + HPKE.size_dh_public cs <= max_size_t /\
    List.Tot.length cipher == AEAD.cipher_length #(HPKE.aead_of_cs cs) (of_list plain)})
  =
  let clength = HPKE.size_dh_public cs + List.Tot.length cipher in
  let expected_pkcipher:lbytes clength = Seq.append (of_list pkE) (of_list cipher) in


  let sealBase = HPKE.sealBase cs (of_list skE) (of_list pkR) (of_list plain) (of_list aad) in
  let res_sealBase =
    if None? sealBase then (
      IO.print_string "sealBase returned None\n"; false
    ) else (
      let returned_pkcipher:lbytes clength = Some?.v sealBase in
      let res = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
        expected_pkcipher returned_pkcipher in
      if not res then (
        IO.print_string "\nExpected pkE + cipher :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list expected_pkcipher);
        IO.print_string "\nComputed pkE + cipher :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_pkcipher);
        IO.print_string "\n");
       res
     )
  in

  if res_sealBase then IO.print_string "sealBase succeeded\n" else IO.print_string "sealBase failed\n";

  let openBase = HPKE.openBase cs (of_list skR) expected_pkcipher (of_list aad) in
  let res_openBase =
    if None? openBase then (
      IO.print_string "openBase returned None\n"; false
    ) else (
      let returned_plain:lbytes (List.Tot.length plain) = Some?.v openBase in
      let res = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b)
        (of_list plain) returned_plain in
      if not res then (
        IO.print_string "\nExpected plain :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) plain;
        IO.print_string "\nComputed plain :";
        List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list returned_plain);
        IO.print_string "\n");
       res
     )
  in

  if res_openBase then IO.print_string "openBase succeeded\n" else IO.print_string "openBase failed\n";


  res_sealBase && res_openBase


//
// Main
//
let test1 () =
  IO.print_string "\nTest 1\n";

  let cs1 = test1_ciphersuite in
  assert_norm (List.Tot.length test1_info <= HPKE.max_info);
  assert_norm (List.Tot.length test1_skR == HPKE.size_dh_key cs1);
  assert_norm (List.Tot.length test1_skI == HPKE.size_dh_key cs1);
  assert_norm (List.Tot.length test1_skE == HPKE.size_dh_key cs1);
//  assert_norm (List.Tot.length test1_pskID <= HPKE.max_pskID);
  assert_norm (List.Tot.length test1_pkR == HPKE.size_dh_public cs1);
  assert_norm (List.Tot.length test1_pkI == HPKE.size_dh_public cs1);
  assert_norm (List.Tot.length test1_pkE == HPKE.size_dh_public cs1);
  assert_norm (List.Tot.length test1_zz == HPKE.size_dh_public cs1);
  // assert_norm (List.Tot.length test1_context == 7 + 3 * HPKE.size_dh_public cs1 + 2 * Hash.size_hash (HPKE.hash_of_cs cs1));

  assert_norm (List.Tot.length test1_key == HPKE.size_aead_key cs1);
  assert_norm (List.Tot.length test1_nonce == HPKE.size_aead_nonce cs1);

  let res1 = test_base_setup cs1 test1_info test1_skR test1_skI test1_skE test1_psk test1_pskID
    test1_pkR test1_pkI test1_pkE test1_enc test1_zz test1_context test1_secret test1_key test1_nonce in

  assert_norm (List.Tot.length test1_cipher0 == 45);
  assert_norm (List.Tot.length test1_plaintext == 29);
  assert_norm (List.Tot.length test1_aad0 <= HPKE.max_info);

  // Cannot be called because Vale has assumed functions in its AES-GCM spec, and
  // tests on the implementation instead
  // let res_encrypt0 = test_encrytion cs1 test1_skE test1_skR test1_pkR test1_pkE test1_plaintext
  //   test1_aad0 test1_cipher0 in

  res1 // && res_encrypt0


let test2 () =
  IO.print_string "\nTest 2\n";

  let cs2 = test2_ciphersuite in

  assert_norm (List.Tot.length test2_info <= HPKE.max_info);
  assert_norm (List.Tot.length test2_skR == HPKE.size_dh_key cs2);
  assert_norm (List.Tot.length test2_skI == HPKE.size_dh_key cs2);
  assert_norm (List.Tot.length test2_skE == HPKE.size_dh_key cs2);

  assert_norm (List.Tot.length test2_pkR == HPKE.size_dh_public cs2);
  assert_norm (List.Tot.length test2_pkI == HPKE.size_dh_public cs2);
  assert_norm (List.Tot.length test2_pkE == HPKE.size_dh_public cs2);
//  assert_norm (List.Tot.length test2_zz == HPKE.size_dh_public cs2);

  true

let test () =
  let r1 = test1 () in
  let r2 = test2 () in
  r1 && r2
