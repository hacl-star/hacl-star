module Spec.HMAC.Test


open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module HMAC = Spec.Agile.HMAC


//
// Test 1
//

let test1_key = List.Tot.map u8_from_UInt8 [
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy
]

let test1_data = List.Tot.map u8_from_UInt8 [
  0x48uy; 0x69uy; 0x20uy; 0x54uy; 0x68uy; 0x65uy; 0x72uy; 0x65uy
]

let test1_expected224 = List.Tot.map u8_from_UInt8 [
  0x89uy; 0x6fuy; 0xb1uy; 0x12uy; 0x8auy; 0xbbuy; 0xdfuy; 0x19uy;
  0x68uy; 0x32uy; 0x10uy; 0x7cuy; 0xd4uy; 0x9duy; 0xf3uy; 0x3fuy;
  0x47uy; 0xb4uy; 0xb1uy; 0x16uy; 0x99uy; 0x12uy; 0xbauy; 0x4fuy;
  0x53uy; 0x68uy; 0x4buy; 0x22uy
]

let test1_expected256 = List.Tot.map u8_from_UInt8 [
  0xb0uy; 0x34uy; 0x4cuy; 0x61uy; 0xd8uy; 0xdbuy; 0x38uy; 0x53uy;
  0x5cuy; 0xa8uy; 0xafuy; 0xceuy; 0xafuy; 0x0buy; 0xf1uy; 0x2buy;
  0x88uy; 0x1duy; 0xc2uy; 0x00uy; 0xc9uy; 0x83uy; 0x3duy; 0xa7uy;
  0x26uy; 0xe9uy; 0x37uy; 0x6cuy; 0x2euy; 0x32uy; 0xcfuy; 0xf7uy
]

let test1_expected384 = List.Tot.map u8_from_UInt8 [
  0xafuy; 0xd0uy; 0x39uy; 0x44uy; 0xd8uy; 0x48uy; 0x95uy; 0x62uy;
  0x6buy; 0x08uy; 0x25uy; 0xf4uy; 0xabuy; 0x46uy; 0x90uy; 0x7fuy;
  0x15uy; 0xf9uy; 0xdauy; 0xdbuy; 0xe4uy; 0x10uy; 0x1euy; 0xc6uy;
  0x82uy; 0xaauy; 0x03uy; 0x4cuy; 0x7cuy; 0xebuy; 0xc5uy; 0x9cuy;
  0xfauy; 0xeauy; 0x9euy; 0xa9uy; 0x07uy; 0x6euy; 0xdeuy; 0x7fuy;
  0x4auy; 0xf1uy; 0x52uy; 0xe8uy; 0xb2uy; 0xfauy; 0x9cuy; 0xb6uy
]

let test1_expected512 = List.Tot.map u8_from_UInt8 [
  0x87uy; 0xaauy; 0x7cuy; 0xdeuy; 0xa5uy; 0xefuy; 0x61uy; 0x9duy;
  0x4fuy; 0xf0uy; 0xb4uy; 0x24uy; 0x1auy; 0x1duy; 0x6cuy; 0xb0uy;
  0x23uy; 0x79uy; 0xf4uy; 0xe2uy; 0xceuy; 0x4euy; 0xc2uy; 0x78uy;
  0x7auy; 0xd0uy; 0xb3uy; 0x05uy; 0x45uy; 0xe1uy; 0x7cuy; 0xdeuy;
  0xdauy; 0xa8uy; 0x33uy; 0xb7uy; 0xd6uy; 0xb8uy; 0xa7uy; 0x02uy;
  0x03uy; 0x8buy; 0x27uy; 0x4euy; 0xaeuy; 0xa3uy; 0xf4uy; 0xe4uy;
  0xbeuy; 0x9duy; 0x91uy; 0x4euy; 0xebuy; 0x61uy; 0xf1uy; 0x70uy;
  0x2euy; 0x69uy; 0x6cuy; 0x20uy; 0x3auy; 0x12uy; 0x68uy; 0x54uy
]

//
// Test 2
//

let test2_key = List.Tot.map u8_from_UInt8 [
  0x4auy; 0x65uy; 0x66uy; 0x65uy
]

let test2_data = List.Tot.map u8_from_UInt8 [
  0x77uy; 0x68uy; 0x61uy; 0x74uy; 0x20uy; 0x64uy; 0x6fuy; 0x20uy;
  0x79uy; 0x61uy; 0x20uy; 0x77uy; 0x61uy; 0x6euy; 0x74uy; 0x20uy;
  0x66uy; 0x6fuy; 0x72uy; 0x20uy; 0x6euy; 0x6fuy; 0x74uy; 0x68uy;
  0x69uy; 0x6euy; 0x67uy; 0x3fuy
]

let test2_expected224 = List.Tot.map u8_from_UInt8 [
  0xa3uy; 0x0euy; 0x01uy; 0x09uy; 0x8buy; 0xc6uy; 0xdbuy; 0xbfuy;
  0x45uy; 0x69uy; 0x0fuy; 0x3auy; 0x7euy; 0x9euy; 0x6duy; 0x0fuy;
  0x8buy; 0xbeuy; 0xa2uy; 0xa3uy; 0x9euy; 0x61uy; 0x48uy; 0x00uy;
  0x8fuy; 0xd0uy; 0x5euy; 0x44uy
]

let test2_expected256 = List.Tot.map u8_from_UInt8 [
  0x5buy; 0xdcuy; 0xc1uy; 0x46uy; 0xbfuy; 0x60uy; 0x75uy; 0x4euy;
  0x6auy; 0x04uy; 0x24uy; 0x26uy; 0x08uy; 0x95uy; 0x75uy; 0xc7uy;
  0x5auy; 0x00uy; 0x3fuy; 0x08uy; 0x9duy; 0x27uy; 0x39uy; 0x83uy;
  0x9duy; 0xecuy; 0x58uy; 0xb9uy; 0x64uy; 0xecuy; 0x38uy; 0x43uy
]

let test2_expected384 = List.Tot.map u8_from_UInt8 [
  0xafuy; 0x45uy; 0xd2uy; 0xe3uy; 0x76uy; 0x48uy; 0x40uy; 0x31uy;
  0x61uy; 0x7fuy; 0x78uy; 0xd2uy; 0xb5uy; 0x8auy; 0x6buy; 0x1buy;
  0x9cuy; 0x7euy; 0xf4uy; 0x64uy; 0xf5uy; 0xa0uy; 0x1buy; 0x47uy;
  0xe4uy; 0x2euy; 0xc3uy; 0x73uy; 0x63uy; 0x22uy; 0x44uy; 0x5euy;
  0x8euy; 0x22uy; 0x40uy; 0xcauy; 0x5euy; 0x69uy; 0xe2uy; 0xc7uy;
  0x8buy; 0x32uy; 0x39uy; 0xecuy; 0xfauy; 0xb2uy; 0x16uy; 0x49uy
]

let test2_expected512 = List.Tot.map u8_from_UInt8 [
  0x16uy; 0x4buy; 0x7auy; 0x7buy; 0xfcuy; 0xf8uy; 0x19uy; 0xe2uy;
  0xe3uy; 0x95uy; 0xfbuy; 0xe7uy; 0x3buy; 0x56uy; 0xe0uy; 0xa3uy;
  0x87uy; 0xbduy; 0x64uy; 0x22uy; 0x2euy; 0x83uy; 0x1fuy; 0xd6uy;
  0x10uy; 0x27uy; 0x0cuy; 0xd7uy; 0xeauy; 0x25uy; 0x05uy; 0x54uy;
  0x97uy; 0x58uy; 0xbfuy; 0x75uy; 0xc0uy; 0x5auy; 0x99uy; 0x4auy;
  0x6duy; 0x03uy; 0x4fuy; 0x65uy; 0xf8uy; 0xf0uy; 0xe6uy; 0xfduy;
  0xcauy; 0xeauy; 0xb1uy; 0xa3uy; 0x4duy; 0x4auy; 0x6buy; 0x4buy;
  0x63uy; 0x6euy; 0x07uy; 0x0auy; 0x38uy; 0xbcuy; 0xe7uy; 0x37uy
]

//
// Test 3
//

let test3_key = List.Tot.map u8_from_UInt8 [
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy
]

let test3_data = List.Tot.map u8_from_UInt8 [
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy
]

let test3_expected224 = List.Tot.map u8_from_UInt8 [
  0x7fuy; 0xb3uy; 0xcbuy; 0x35uy; 0x88uy; 0xc6uy; 0xc1uy; 0xf6uy;
  0xffuy; 0xa9uy; 0x69uy; 0x4duy; 0x7duy; 0x6auy; 0xd2uy; 0x64uy;
  0x93uy; 0x65uy; 0xb0uy; 0xc1uy; 0xf6uy; 0x5duy; 0x69uy; 0xd1uy;
  0xecuy; 0x83uy; 0x33uy; 0xeauy
]

let test3_expected256 = List.Tot.map u8_from_UInt8 [
  0x77uy; 0x3euy; 0xa9uy; 0x1euy; 0x36uy; 0x80uy; 0x0euy; 0x46uy;
  0x85uy; 0x4duy; 0xb8uy; 0xebuy; 0xd0uy; 0x91uy; 0x81uy; 0xa7uy;
  0x29uy; 0x59uy; 0x09uy; 0x8buy; 0x3euy; 0xf8uy; 0xc1uy; 0x22uy;
  0xd9uy; 0x63uy; 0x55uy; 0x14uy; 0xceuy; 0xd5uy; 0x65uy; 0xfeuy
]

let test3_expected384 = List.Tot.map u8_from_UInt8 [
  0x88uy; 0x06uy; 0x26uy; 0x08uy; 0xd3uy; 0xe6uy; 0xaduy; 0x8auy;
  0x0auy; 0xa2uy; 0xacuy; 0xe0uy; 0x14uy; 0xc8uy; 0xa8uy; 0x6fuy;
  0x0auy; 0xa6uy; 0x35uy; 0xd9uy; 0x47uy; 0xacuy; 0x9fuy; 0xebuy;
  0xe8uy; 0x3euy; 0xf4uy; 0xe5uy; 0x59uy; 0x66uy; 0x14uy; 0x4buy;
  0x2auy; 0x5auy; 0xb3uy; 0x9duy; 0xc1uy; 0x38uy; 0x14uy; 0xb9uy;
  0x4euy; 0x3auy; 0xb6uy; 0xe1uy; 0x01uy; 0xa3uy; 0x4fuy; 0x27uy
]

let test3_expected512 = List.Tot.map u8_from_UInt8 [
  0xfauy; 0x73uy; 0xb0uy; 0x08uy; 0x9duy; 0x56uy; 0xa2uy; 0x84uy;
  0xefuy; 0xb0uy; 0xf0uy; 0x75uy; 0x6cuy; 0x89uy; 0x0buy; 0xe9uy;
  0xb1uy; 0xb5uy; 0xdbuy; 0xdduy; 0x8euy; 0xe8uy; 0x1auy; 0x36uy;
  0x55uy; 0xf8uy; 0x3euy; 0x33uy; 0xb2uy; 0x27uy; 0x9duy; 0x39uy;
  0xbfuy; 0x3euy; 0x84uy; 0x82uy; 0x79uy; 0xa7uy; 0x22uy; 0xc8uy;
  0x06uy; 0xb4uy; 0x85uy; 0xa4uy; 0x7euy; 0x67uy; 0xc8uy; 0x07uy;
  0xb9uy; 0x46uy; 0xa3uy; 0x37uy; 0xbeuy; 0xe8uy; 0x94uy; 0x26uy;
  0x74uy; 0x27uy; 0x88uy; 0x59uy; 0xe1uy; 0x32uy; 0x92uy; 0xfbuy
]

//
// Test 4
//

let test4_key = List.Tot.map u8_from_UInt8 [
  0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy; 0x08uy;
  0x09uy; 0x0auy; 0x0buy; 0x0cuy; 0x0duy; 0x0euy; 0x0fuy; 0x10uy;
  0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy; 0x18uy;
  0x19uy
]

let test4_data = List.Tot.map u8_from_UInt8 [
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy
]

let test4_expected224 = List.Tot.map u8_from_UInt8 [
  0x6cuy; 0x11uy; 0x50uy; 0x68uy; 0x74uy; 0x01uy; 0x3cuy; 0xacuy;
  0x6auy; 0x2auy; 0xbcuy; 0x1buy; 0xb3uy; 0x82uy; 0x62uy; 0x7cuy;
  0xecuy; 0x6auy; 0x90uy; 0xd8uy; 0x6euy; 0xfcuy; 0x01uy; 0x2duy;
  0xe7uy; 0xafuy; 0xecuy; 0x5auy

]

let test4_expected256 = List.Tot.map u8_from_UInt8 [
  0x82uy; 0x55uy; 0x8auy; 0x38uy; 0x9auy; 0x44uy; 0x3cuy; 0x0euy;
  0xa4uy; 0xccuy; 0x81uy; 0x98uy; 0x99uy; 0xf2uy; 0x08uy; 0x3auy;
  0x85uy; 0xf0uy; 0xfauy; 0xa3uy; 0xe5uy; 0x78uy; 0xf8uy; 0x07uy;
  0x7auy; 0x2euy; 0x3fuy; 0xf4uy; 0x67uy; 0x29uy; 0x66uy; 0x5buy
]

let test4_expected384 = List.Tot.map u8_from_UInt8 [
  0x3euy; 0x8auy; 0x69uy; 0xb7uy; 0x78uy; 0x3cuy; 0x25uy; 0x85uy;
  0x19uy; 0x33uy; 0xabuy; 0x62uy; 0x90uy; 0xafuy; 0x6cuy; 0xa7uy;
  0x7auy; 0x99uy; 0x81uy; 0x48uy; 0x08uy; 0x50uy; 0x00uy; 0x9cuy;
  0xc5uy; 0x57uy; 0x7cuy; 0x6euy; 0x1fuy; 0x57uy; 0x3buy; 0x4euy;
  0x68uy; 0x01uy; 0xdduy; 0x23uy; 0xc4uy; 0xa7uy; 0xd6uy; 0x79uy;
  0xccuy; 0xf8uy; 0xa3uy; 0x86uy; 0xc6uy; 0x74uy; 0xcfuy; 0xfbuy
]

let test4_expected512 = List.Tot.map u8_from_UInt8 [
  0xb0uy; 0xbauy; 0x46uy; 0x56uy; 0x37uy; 0x45uy; 0x8cuy; 0x69uy;
  0x90uy; 0xe5uy; 0xa8uy; 0xc5uy; 0xf6uy; 0x1duy; 0x4auy; 0xf7uy;
  0xe5uy; 0x76uy; 0xd9uy; 0x7fuy; 0xf9uy; 0x4buy; 0x87uy; 0x2duy;
  0xe7uy; 0x6fuy; 0x80uy; 0x50uy; 0x36uy; 0x1euy; 0xe3uy; 0xdbuy;
  0xa9uy; 0x1cuy; 0xa5uy; 0xc1uy; 0x1auy; 0xa2uy; 0x5euy; 0xb4uy;
  0xd6uy; 0x79uy; 0x27uy; 0x5cuy; 0xc5uy; 0x78uy; 0x80uy; 0x63uy;
  0xa5uy; 0xf1uy; 0x97uy; 0x41uy; 0x12uy; 0x0cuy; 0x4fuy; 0x2duy;
  0xe2uy; 0xaduy; 0xebuy; 0xebuy; 0x10uy; 0xa2uy; 0x98uy; 0xdduy
]

//
// Test 5
//

let test5_key = List.Tot.map u8_from_UInt8 [
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy;
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy;
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy
]

let test5_data = List.Tot.map u8_from_UInt8 [
  0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x57uy; 0x69uy; 0x74uy;
  0x68uy; 0x20uy; 0x54uy; 0x72uy; 0x75uy; 0x6euy; 0x63uy; 0x61uy;
  0x74uy; 0x69uy; 0x6fuy; 0x6euy
]

let test5_expected224 = List.Tot.map u8_from_UInt8 [
  0x0euy; 0x2auy; 0xeauy; 0x68uy; 0xa9uy; 0x0cuy; 0x8duy; 0x37uy;
  0xc9uy; 0x88uy; 0xbcuy; 0xdbuy; 0x9fuy; 0xcauy; 0x6fuy; 0xa8uy;
]

let test5_expected256 = List.Tot.map u8_from_UInt8 [
  0xa3uy; 0xb6uy; 0x16uy; 0x74uy; 0x73uy; 0x10uy; 0x0euy; 0xe0uy;
  0x6euy; 0x0cuy; 0x79uy; 0x6cuy; 0x29uy; 0x55uy; 0x55uy; 0x2buy
]

let test5_expected384 = List.Tot.map u8_from_UInt8 [
  0x3auy; 0xbfuy; 0x34uy; 0xc3uy; 0x50uy; 0x3buy; 0x2auy; 0x23uy;
  0xa4uy; 0x6euy; 0xfcuy; 0x61uy; 0x9buy; 0xaeuy; 0xf8uy; 0x97uy
]

let test5_expected512 = List.Tot.map u8_from_UInt8 [
  0x41uy; 0x5fuy; 0xaduy; 0x62uy; 0x71uy; 0x58uy; 0x0auy; 0x53uy;
  0x1duy; 0x41uy; 0x79uy; 0xbcuy; 0x89uy; 0x1duy; 0x87uy; 0xa6uy
]

//
// Test 6
//

let test6_key = List.Tot.map u8_from_UInt8 [
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy
]

let test6_data = List.Tot.map u8_from_UInt8 [
  0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x55uy; 0x73uy; 0x69uy;
  0x6euy; 0x67uy; 0x20uy; 0x4cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy;
  0x72uy; 0x20uy; 0x54uy; 0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x42uy;
  0x6cuy; 0x6fuy; 0x63uy; 0x6buy; 0x2duy; 0x53uy; 0x69uy; 0x7auy;
  0x65uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy; 0x20uy; 0x2duy; 0x20uy;
  0x48uy; 0x61uy; 0x73uy; 0x68uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy;
  0x20uy; 0x46uy; 0x69uy; 0x72uy; 0x73uy; 0x74uy
]

let test6_expected224 = List.Tot.map u8_from_UInt8 [
  0x95uy; 0xe9uy; 0xa0uy; 0xdbuy; 0x96uy; 0x20uy; 0x95uy; 0xaduy;
  0xaeuy; 0xbeuy; 0x9buy; 0x2duy; 0x6fuy; 0x0duy; 0xbcuy; 0xe2uy;
  0xd4uy; 0x99uy; 0xf1uy; 0x12uy; 0xf2uy; 0xd2uy; 0xb7uy; 0x27uy;
  0x3fuy; 0xa6uy; 0x87uy; 0x0euy
]

let test6_expected256 = List.Tot.map u8_from_UInt8 [
  0x60uy; 0xe4uy; 0x31uy; 0x59uy; 0x1euy; 0xe0uy; 0xb6uy; 0x7fuy;
  0x0duy; 0x8auy; 0x26uy; 0xaauy; 0xcbuy; 0xf5uy; 0xb7uy; 0x7fuy;
  0x8euy; 0x0buy; 0xc6uy; 0x21uy; 0x37uy; 0x28uy; 0xc5uy; 0x14uy;
  0x05uy; 0x46uy; 0x04uy; 0x0fuy; 0x0euy; 0xe3uy; 0x7fuy; 0x54uy
]

let test6_expected384 = List.Tot.map u8_from_UInt8 [
  0x4euy; 0xceuy; 0x08uy; 0x44uy; 0x85uy; 0x81uy; 0x3euy; 0x90uy;
  0x88uy; 0xd2uy; 0xc6uy; 0x3auy; 0x04uy; 0x1buy; 0xc5uy; 0xb4uy;
  0x4fuy; 0x9euy; 0xf1uy; 0x01uy; 0x2auy; 0x2buy; 0x58uy; 0x8fuy;
  0x3cuy; 0xd1uy; 0x1fuy; 0x05uy; 0x03uy; 0x3auy; 0xc4uy; 0xc6uy;
  0x0cuy; 0x2euy; 0xf6uy; 0xabuy; 0x40uy; 0x30uy; 0xfeuy; 0x82uy;
  0x96uy; 0x24uy; 0x8duy; 0xf1uy; 0x63uy; 0xf4uy; 0x49uy; 0x52uy
]

let test6_expected512 = List.Tot.map u8_from_UInt8 [
  0x80uy; 0xb2uy; 0x42uy; 0x63uy; 0xc7uy; 0xc1uy; 0xa3uy; 0xebuy;
  0xb7uy; 0x14uy; 0x93uy; 0xc1uy; 0xdduy; 0x7buy; 0xe8uy; 0xb4uy;
  0x9buy; 0x46uy; 0xd1uy; 0xf4uy; 0x1buy; 0x4auy; 0xeeuy; 0xc1uy;
  0x12uy; 0x1buy; 0x01uy; 0x37uy; 0x83uy; 0xf8uy; 0xf3uy; 0x52uy;
  0x6buy; 0x56uy; 0xd0uy; 0x37uy; 0xe0uy; 0x5fuy; 0x25uy; 0x98uy;
  0xbduy; 0x0fuy; 0xd2uy; 0x21uy; 0x5duy; 0x6auy; 0x1euy; 0x52uy;
  0x95uy; 0xe6uy; 0x4fuy; 0x73uy; 0xf6uy; 0x3fuy; 0x0auy; 0xecuy;
  0x8buy; 0x91uy; 0x5auy; 0x98uy; 0x5duy; 0x78uy; 0x65uy; 0x98uy
]

//
// Test 7
//

let test7_key = List.Tot.map u8_from_UInt8 [
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy
]

let test7_data = List.Tot.map u8_from_UInt8 [
  0x54uy; 0x68uy; 0x69uy; 0x73uy; 0x20uy; 0x69uy; 0x73uy; 0x20uy;
  0x61uy; 0x20uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x75uy;
  0x73uy; 0x69uy; 0x6euy; 0x67uy; 0x20uy; 0x61uy; 0x20uy; 0x6cuy;
  0x61uy; 0x72uy; 0x67uy; 0x65uy; 0x72uy; 0x20uy; 0x74uy; 0x68uy;
  0x61uy; 0x6euy; 0x20uy; 0x62uy; 0x6cuy; 0x6fuy; 0x63uy; 0x6buy;
  0x2duy; 0x73uy; 0x69uy; 0x7auy; 0x65uy; 0x20uy; 0x6buy; 0x65uy;
  0x79uy; 0x20uy; 0x61uy; 0x6euy; 0x64uy; 0x20uy; 0x61uy; 0x20uy;
  0x6cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy; 0x72uy; 0x20uy; 0x74uy;
  0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x62uy; 0x6cuy; 0x6fuy; 0x63uy;
  0x6buy; 0x2duy; 0x73uy; 0x69uy; 0x7auy; 0x65uy; 0x20uy; 0x64uy;
  0x61uy; 0x74uy; 0x61uy; 0x2euy; 0x20uy; 0x54uy; 0x68uy; 0x65uy;
  0x20uy; 0x6buy; 0x65uy; 0x79uy; 0x20uy; 0x6euy; 0x65uy; 0x65uy;
  0x64uy; 0x73uy; 0x20uy; 0x74uy; 0x6fuy; 0x20uy; 0x62uy; 0x65uy;
  0x20uy; 0x68uy; 0x61uy; 0x73uy; 0x68uy; 0x65uy; 0x64uy; 0x20uy;
  0x62uy; 0x65uy; 0x66uy; 0x6fuy; 0x72uy; 0x65uy; 0x20uy; 0x62uy;
  0x65uy; 0x69uy; 0x6euy; 0x67uy; 0x20uy; 0x75uy; 0x73uy; 0x65uy;
  0x64uy; 0x20uy; 0x62uy; 0x79uy; 0x20uy; 0x74uy; 0x68uy; 0x65uy;
  0x20uy; 0x48uy; 0x4duy; 0x41uy; 0x43uy; 0x20uy; 0x61uy; 0x6cuy;
  0x67uy; 0x6fuy; 0x72uy; 0x69uy; 0x74uy; 0x68uy; 0x6duy; 0x2euy
]

let test7_expected224 = List.Tot.map u8_from_UInt8 [
  0x3auy; 0x85uy; 0x41uy; 0x66uy; 0xacuy; 0x5duy; 0x9fuy; 0x02uy;
  0x3fuy; 0x54uy; 0xd5uy; 0x17uy; 0xd0uy; 0xb3uy; 0x9duy; 0xbduy;
  0x94uy; 0x67uy; 0x70uy; 0xdbuy; 0x9cuy; 0x2buy; 0x95uy; 0xc9uy;
  0xf6uy; 0xf5uy; 0x65uy; 0xd1uy
]

let test7_expected256 = List.Tot.map u8_from_UInt8 [
  0x9buy; 0x09uy; 0xffuy; 0xa7uy; 0x1buy; 0x94uy; 0x2fuy; 0xcbuy;
  0x27uy; 0x63uy; 0x5fuy; 0xbcuy; 0xd5uy; 0xb0uy; 0xe9uy; 0x44uy;
  0xbfuy; 0xdcuy; 0x63uy; 0x64uy; 0x4fuy; 0x07uy; 0x13uy; 0x93uy;
  0x8auy; 0x7fuy; 0x51uy; 0x53uy; 0x5cuy; 0x3auy; 0x35uy; 0xe2uy
]

let test7_expected384 = List.Tot.map u8_from_UInt8 [
  0x66uy; 0x17uy; 0x17uy; 0x8euy; 0x94uy; 0x1fuy; 0x02uy; 0x0duy;
  0x35uy; 0x1euy; 0x2fuy; 0x25uy; 0x4euy; 0x8fuy; 0xd3uy; 0x2cuy;
  0x60uy; 0x24uy; 0x20uy; 0xfeuy; 0xb0uy; 0xb8uy; 0xfbuy; 0x9auy;
  0xdcuy; 0xceuy; 0xbbuy; 0x82uy; 0x46uy; 0x1euy; 0x99uy; 0xc5uy;
  0xa6uy; 0x78uy; 0xccuy; 0x31uy; 0xe7uy; 0x99uy; 0x17uy; 0x6duy;
  0x38uy; 0x60uy; 0xe6uy; 0x11uy; 0x0cuy; 0x46uy; 0x52uy; 0x3euy
]

let test7_expected512 = List.Tot.map u8_from_UInt8 [
  0xe3uy; 0x7buy; 0x6auy; 0x77uy; 0x5duy; 0xc8uy; 0x7duy; 0xbauy;
  0xa4uy; 0xdfuy; 0xa9uy; 0xf9uy; 0x6euy; 0x5euy; 0x3fuy; 0xfduy;
  0xdeuy; 0xbduy; 0x71uy; 0xf8uy; 0x86uy; 0x72uy; 0x89uy; 0x86uy;
  0x5duy; 0xf5uy; 0xa3uy; 0x2duy; 0x20uy; 0xcduy; 0xc9uy; 0x44uy;
  0xb6uy; 0x02uy; 0x2cuy; 0xacuy; 0x3cuy; 0x49uy; 0x82uy; 0xb1uy;
  0x0duy; 0x5euy; 0xebuy; 0x55uy; 0xc3uy; 0xe4uy; 0xdeuy; 0x15uy;
  0x13uy; 0x46uy; 0x76uy; 0xfbuy; 0x6duy; 0xe0uy; 0x44uy; 0x60uy;
  0x65uy; 0xc9uy; 0x74uy; 0x40uy; 0xfauy; 0x8cuy; 0x6auy; 0x58uy
]

//
// Main
//

let test () =

  IO.print_string "\nTEST 1\n";
  let test1_key_len : size_nat = 20 in
  let test1_key : lbytes test1_key_len = of_list test1_key in
  let test1_data_len : size_nat = 8 in
  let test1_data : lbytes test1_data_len = of_list test1_data in
  let test1_expected224 = of_list test1_expected224 in
  let test1_expected256 = of_list test1_expected256 in
  let test1_expected384 = of_list test1_expected384 in
  let test1_expected512 = of_list test1_expected512 in
  let test1_result224 = HMAC.hmac Spec.Hash.Definitions.SHA2_224 test1_key test1_data in
  let test1_result256 = HMAC.hmac Spec.Hash.Definitions.SHA2_256 test1_key test1_data in
  let test1_result384 = HMAC.hmac Spec.Hash.Definitions.SHA2_384 test1_key test1_data in
  let test1_result512 = HMAC.hmac Spec.Hash.Definitions.SHA2_512 test1_key test1_data in
  let result1_224 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected224 test1_result224 in
  let result1_256 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected256 test1_result256 in
  let result1_384 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected384 test1_result384 in
  let result1_512 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected512 test1_result512 in
  let result1 = result1_224 && result1_256 && result1_384 && result1_512 in
  IO.print_string "\nExpected HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_expected224);
  IO.print_string "\nComputed HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_result224);
  IO.print_string "\nExpected HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_expected256);
  IO.print_string "\nComputed HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_result256);
  IO.print_string "\nExpected HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_expected384);
  IO.print_string "\nComputed HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_result384);
  IO.print_string "\nExpected HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_expected512);
  IO.print_string "\nComputed HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_result512);

  if result1 then IO.print_string "\nHMAC SHA2 Test1 ontime: Success!\n"
  else IO.print_string "\nHMAC SHA2 Test1 ontime: Failure :(\n";


  IO.print_string "\nTEST 2\n";
  let test2_key_len : size_nat = List.Tot.length test2_key in
  let test2_key : lbytes test2_key_len = of_list test2_key in
  let test2_data_len : size_nat = List.Tot.length test2_data in
  let test2_data : lbytes test2_data_len = of_list test2_data in
  let test2_expected224 = of_list test2_expected224 in
  let test2_expected256 = of_list test2_expected256 in
  let test2_expected384 = of_list test2_expected384 in
  let test2_expected512 = of_list test2_expected512 in
  let test2_result224 = HMAC.hmac Spec.Hash.Definitions.SHA2_224 test2_key test2_data in
  let test2_result256 = HMAC.hmac Spec.Hash.Definitions.SHA2_256 test2_key test2_data in
  let test2_result384 = HMAC.hmac Spec.Hash.Definitions.SHA2_384 test2_key test2_data in
  let test2_result512 = HMAC.hmac Spec.Hash.Definitions.SHA2_512 test2_key test2_data in
  let result2_224 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test2_expected224 test2_result224 in
  let result2_256 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test2_expected256 test2_result256 in
  let result2_384 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test2_expected384 test2_result384 in
  let result2_512 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test2_expected512 test2_result512 in
  let result2 = result2_224 && result2_256 && result2_384 && result2_512 in

  IO.print_string "\nExpected HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_expected224);
  IO.print_string "\nComputed HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_result224);
  IO.print_string "\nExpected HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_expected256);
  IO.print_string "\nComputed HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_result256);
  IO.print_string "\nExpected HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_expected384);
  IO.print_string "\nComputed HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_result384);
  IO.print_string "\nExpected HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_expected512);
  IO.print_string "\nComputed HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_result512);

  if result2 then IO.print_string "\nHMAC SHA2 Test2 ontime: Success!\n"
  else IO.print_string "\nHMAC SHA2 Test2 ontime: Failure :(\n";

  IO.print_string "\nTEST 3\n";
  let test3_key_len : size_nat = List.Tot.length test3_key in
  let test3_key : lbytes test3_key_len = of_list test3_key in
  let test3_data_len : size_nat = List.Tot.length test3_data in
  let test3_data : lbytes test3_data_len = of_list test3_data in
  let test3_expected224 = of_list test3_expected224 in
  let test3_expected256 = of_list test3_expected256 in
  let test3_expected384 = of_list test3_expected384 in
  let test3_expected512 = of_list test3_expected512 in
  let test3_result224 = HMAC.hmac Spec.Hash.Definitions.SHA2_224 test3_key test3_data in
  let test3_result256 = HMAC.hmac Spec.Hash.Definitions.SHA2_256 test3_key test3_data in
  let test3_result384 = HMAC.hmac Spec.Hash.Definitions.SHA2_384 test3_key test3_data in
  let test3_result512 = HMAC.hmac Spec.Hash.Definitions.SHA2_512 test3_key test3_data in
  let result3_224 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test3_expected224 test3_result224 in
  let result3_256 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test3_expected256 test3_result256 in
  let result3_384 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test3_expected384 test3_result384 in
  let result3_512 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test3_expected512 test3_result512 in
  let result3 = result3_224 && result3_256 && result3_384 && result3_512 in

  IO.print_string "\nExpected HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_expected224);
  IO.print_string "\nComputed HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_result224);
  IO.print_string "\nExpected HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_expected256);
  IO.print_string "\nComputed HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_result256);
  IO.print_string "\nExpected HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_expected384);
  IO.print_string "\nComputed HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_result384);
  IO.print_string "\nExpected HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_expected512);
  IO.print_string "\nComputed HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_result512);

  if result3 then IO.print_string "\nHMAC SHA2 Test3 ontime: Success!\n"
  else IO.print_string "\nHMAC SHA2 Test3 ontime: Failure :(\n";

  IO.print_string "\nTEST 4\n";
  let test4_key_len : size_nat = List.Tot.length test4_key in
  let test4_key : lbytes test4_key_len = of_list test4_key in
  let test4_data_len : size_nat = List.Tot.length test4_data in
  let test4_data : lbytes test4_data_len = of_list test4_data in
  let test4_expected224 = of_list test4_expected224 in
  let test4_expected256 = of_list test4_expected256 in
  let test4_expected384 = of_list test4_expected384 in
  let test4_expected512 = of_list test4_expected512 in
  let test4_result224 = HMAC.hmac Spec.Hash.Definitions.SHA2_224 test4_key test4_data in
  let test4_result256 = HMAC.hmac Spec.Hash.Definitions.SHA2_256 test4_key test4_data in
  let test4_result384 = HMAC.hmac Spec.Hash.Definitions.SHA2_384 test4_key test4_data in
  let test4_result512 = HMAC.hmac Spec.Hash.Definitions.SHA2_512 test4_key test4_data in
  let result4_224 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test4_expected224 test4_result224 in
  let result4_256 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test4_expected256 test4_result256 in
  let result4_384 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test4_expected384 test4_result384 in
  let result4_512 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test4_expected512 test4_result512 in
  let result4 = result4_224 && result4_256 && result4_384 && result4_512 in

  IO.print_string "\nExpected HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test4_expected224);
  IO.print_string "\nComputed HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test4_result224);
  IO.print_string "\nExpected HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test4_expected256);
  IO.print_string "\nComputed HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test4_result256);
  IO.print_string "\nExpected HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test4_expected384);
  IO.print_string "\nComputed HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test4_result384);
  IO.print_string "\nExpected HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test4_expected512);
  IO.print_string "\nComputed HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test4_result512);

  if result4 then IO.print_string "\nHMAC SHA2 Test4 ontime: Success!\n"
  else IO.print_string "\nHMAC SHA2 Test4 ontime: Failure :(\n";

  IO.print_string "\nTEST 5\n";
  let test5_key_len : size_nat = List.Tot.length test5_key in
  let test5_key : lbytes test5_key_len = of_list test5_key in
  let test5_data_len : size_nat = List.Tot.length test5_data in
  let test5_data : lbytes test5_data_len = of_list test5_data in
  let test5_expected224 : lbytes 16 = of_list test5_expected224 in
  let test5_expected256 : lbytes 16 = of_list test5_expected256 in
  let test5_expected384 : lbytes 16 = of_list test5_expected384 in
  let test5_expected512 : lbytes 16 = of_list test5_expected512 in
  let test5_result224b = HMAC.hmac Spec.Hash.Definitions.SHA2_224 test5_key test5_data in
  let test5_result256b = HMAC.hmac Spec.Hash.Definitions.SHA2_256 test5_key test5_data in
  let test5_result384b = HMAC.hmac Spec.Hash.Definitions.SHA2_384 test5_key test5_data in
  let test5_result512b = HMAC.hmac Spec.Hash.Definitions.SHA2_512 test5_key test5_data in
  let test5_result224 = Seq.slice test5_result224b 0 16 in
  let test5_result256 = Seq.slice test5_result256b 0 16 in
  let test5_result384 = Seq.slice test5_result384b 0 16 in
  let test5_result512 = Seq.slice test5_result512b 0 16 in
  let result5_224 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test5_expected224 test5_result224 in
  let result5_256 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test5_expected256 test5_result256 in
  let result5_384 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test5_expected384 test5_result384 in
  let result5_512 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test5_expected512 test5_result512 in
  let result5 = result5_224 && result5_256 && result5_384 && result5_512 in

  IO.print_string "\nExpected HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test5_expected224);
  IO.print_string "\nComputed HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test5_result224);
  IO.print_string "\nExpected HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test5_expected256);
  IO.print_string "\nComputed HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test5_result256);
  IO.print_string "\nExpected HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test5_expected384);
  IO.print_string "\nComputed HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test5_result384);
  IO.print_string "\nExpected HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test5_expected512);
  IO.print_string "\nComputed HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test5_result512);

  if result5 then IO.print_string "\nHMAC SHA2 Test5 ontime: Success!\n"
  else IO.print_string "\nHMAC SHA2 Test5 ontime: Failure :(\n";


  IO.print_string "\nTEST 6\n";
  let test6_key_len : size_nat = List.Tot.length test6_key in
  let test6_key : lbytes test6_key_len = of_list test6_key in
  let test6_data_len : size_nat = List.Tot.length test6_data in
  let test6_data : lbytes test6_data_len = of_list test6_data in
  let test6_expected224 = of_list test6_expected224 in
  let test6_expected256 = of_list test6_expected256 in
  let test6_expected384 = of_list test6_expected384 in
  let test6_expected512 = of_list test6_expected512 in
  let test6_result224 = HMAC.hmac Spec.Hash.Definitions.SHA2_224 test6_key test6_data in
  let test6_result256 = HMAC.hmac Spec.Hash.Definitions.SHA2_256 test6_key test6_data in
  let test6_result384 = HMAC.hmac Spec.Hash.Definitions.SHA2_384 test6_key test6_data in
  let test6_result512 = HMAC.hmac Spec.Hash.Definitions.SHA2_512 test6_key test6_data in
  let result6_224 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test6_expected224 test6_result224 in
  let result6_256 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test6_expected256 test6_result256 in
  let result6_384 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test6_expected384 test6_result384 in
  let result6_512 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test6_expected512 test6_result512 in
  let result6 = result6_224 && result6_256 && result6_384 && result6_512 in

  IO.print_string "\nExpected HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test6_expected224);
  IO.print_string "\nComputed HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test6_result224);
  IO.print_string "\nExpected HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test6_expected256);
  IO.print_string "\nComputed HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test6_result256);
  IO.print_string "\nExpected HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test6_expected384);
  IO.print_string "\nComputed HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test6_result384);
  IO.print_string "\nExpected HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test6_expected512);
  IO.print_string "\nComputed HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test6_result512);

  if result6 then IO.print_string "\nHMAC SHA2 Test6 ontime: Success!\n"
  else IO.print_string "\nHMAC SHA2 Test6 ontime: Failure :(\n";


  IO.print_string "\nTEST 7\n";
  let test7_key_len : size_nat = List.Tot.length test7_key in
  let test7_key : lbytes test7_key_len = of_list test7_key in
  let test7_data_len : size_nat = List.Tot.length test7_data in
  let test7_data : lbytes test7_data_len = of_list test7_data in
  let test7_expected224 = of_list test7_expected224 in
  let test7_expected256 = of_list test7_expected256 in
  let test7_expected384 = of_list test7_expected384 in
  let test7_expected512 = of_list test7_expected512 in
  let test7_result224 = HMAC.hmac Spec.Hash.Definitions.SHA2_224 test7_key test7_data in
  let test7_result256 = HMAC.hmac Spec.Hash.Definitions.SHA2_256 test7_key test7_data in
  let test7_result384 = HMAC.hmac Spec.Hash.Definitions.SHA2_384 test7_key test7_data in
  let test7_result512  = HMAC.hmac Spec.Hash.Definitions.SHA2_512 test7_key test7_data in
  let result7_224 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test7_expected224 test7_result224 in
  let result7_256 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test7_expected256 test7_result256 in
  let result7_384 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test7_expected384 test7_result384 in
  let result7_512 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test7_expected512 test7_result512 in
  let result7 = result7_224 && result7_256 && result7_384 && result7_512 in

  IO.print_string "\nExpected HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test7_expected224);
  IO.print_string "\nComputed HMAC SHA2 224: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test7_result224);
  IO.print_string "\nExpected HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test7_expected256);
  IO.print_string "\nComputed HMAC SHA2 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test7_result256);
  IO.print_string "\nExpected HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test7_expected384);
  IO.print_string "\nComputed HMAC SHA2 384: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test7_result384);
  IO.print_string "\nExpected HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test7_expected512);
  IO.print_string "\nComputed HMAC SHA2 512: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test7_result512);

  if result7 then IO.print_string "\nHMAC SHA2 Test7 ontime: Success!\n"
  else IO.print_string "\nHMAC SHA2 Test7 ontime: Failure :(\n";


  if result1 && result2 && result3 && result4 && result5 && result6 && result7 then begin IO.print_string "\nComposite result: Success!\n"; true end
  else begin IO.print_string "\nComposite result: Failure :(\n"; false end
