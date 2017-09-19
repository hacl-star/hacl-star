module Spec.HSalsa20

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Seq.Create
open Spec.Lib
open Spec.Salsa20

let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 16  (* in bytes *)

type key = lbytes keylen
type nonce = lbytes noncelen
type block = lbytes blocklen

type state = Salsa20.state

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let setup (k:key) (n:nonce): state =
  let ks = uint32s_from_le 8 k in
  let ns = uint32s_from_le 4 n in
  let k_fst_half = slice ks 0 4 in
  let k_snd_half = slice ks 4 8 in
  create_16 Salsa20.constant0 (index ks 0)      (index ks 1)      (index ks 2)
          (index ks 3)       Salsa20.constant1 (index ns 0)      (index ns 1)
    (index ns 2)       (index ns 3)      Salsa20.constant2 (index ks 4)
          (index ks 5)       (index ks 6)      (index ks 7)      Salsa20.constant3

let hsalsa20 (k:key) (n:nonce) : Tot key =
  let st = setup k n in
  let st' = Spec.Salsa20.rounds st in
  let hs = create_8 st'.[0] st'.[5] st'.[10] st'.[15] st'.[6] st'.[7] st'.[8] st'.[9] in
  uint32s_to_le 8 hs

(* Tests: https://cr.yp.to/highspeed/naclcrypto-20090310.pdf (Section 8)*)
unfold let k = [
       0x4auy;0x5duy;0x9duy;0x5buy;0xa4uy;0xceuy;0x2duy;0xe1uy;
       0x72uy;0x8euy;0x3buy;0xf4uy;0x80uy;0x35uy;0x0fuy;0x25uy;
       0xe0uy;0x7euy;0x21uy;0xc9uy;0x47uy;0xd1uy;0x9euy;0x33uy;
       0x76uy;0xf0uy;0x9buy;0x3cuy;0x1euy;0x16uy;0x17uy;0x42uy]

unfold let zero = [
       0x00uy;0x00uy;0x00uy;0x00uy;0x00uy;0x00uy;0x00uy;0x00uy;
       0x00uy;0x00uy;0x00uy;0x00uy;0x00uy;0x00uy;0x00uy;0x00uy]

unfold let k1 = [
       0x1buy;0x27uy;0x55uy;0x64uy;0x73uy;0xe9uy;0x85uy;0xd4uy;
       0x62uy;0xcduy;0x51uy;0x19uy;0x7auy;0x9auy;0x46uy;0xc7uy;
       0x60uy;0x09uy;0x54uy;0x9euy;0xacuy;0x64uy;0x74uy;0xf2uy;
       0x06uy;0xc4uy;0xeeuy;0x08uy;0x44uy;0xf6uy;0x83uy;0x89uy]


let test() =
    assert_norm(List.Tot.length k = 32);
    assert_norm(List.Tot.length zero = 16);
    assert_norm(List.Tot.length k1 = 32);
    let k = createL k in
    let zero = createL zero in
    let k1 = createL k1 in
    let k1' = hsalsa20 k zero in
    k1 = k1'
