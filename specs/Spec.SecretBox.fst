module Spec.SecretBox

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open Lib.LoopCombinators

#set-options "--z3rlimit 100"
(* Constants *)
let size_key = 32 (* in bytes *)
let size_nonce = 24   (* in bytes *)
let size_block = 64   (* in bytes *)
let size_tag = 16 (* in bytes *)

type key = lbytes size_key
type aekey = lbytes (size_key + size_key)
type nonce = lbytes size_nonce
type tag = lbytes size_tag

let secretbox_init (k:key) (n:nonce) : key & aekey =
  let n0 : lbytes 16 = sub n 0 16 in
  let n1 : lbytes 8 = sub n 16 8 in
  let subkey : lbytes 32 = Spec.Salsa20.hsalsa20 k n0 in
  let aekey : lbytes 64 = Spec.Salsa20.salsa20_key_block0 subkey n1 in
  (subkey,aekey)

let secretbox_detached (k:key) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : (tag & c:bytes{length c = length m}) =
  let (subkey,aekey) = secretbox_init k n in
  let n1 = sub n 16 8 in
  let mkey = sub aekey 0 32 in
  let ekey0 = sub aekey 32 32 in
  let block0 = create 32 (u8 0) in
  let mlen0 = if length m <= 32 then length m else 32 in
  let m0 = Seq.slice m 0 mlen0 in
  let m1 = Seq.slice m mlen0 (length m) in
  let block0 = update_sub block0 0 mlen0 m0 in
  let block0 = map2 (^.) block0 ekey0 in
  let c0 = sub block0 0 mlen0 in
  assert (length m1 / size_block <= max_size_t);
  assert (length m = length m0 + length m1);
  let c1 = Spec.Salsa20.salsa20_encrypt_bytes subkey n1 1 m1 in
  let c = Seq.append c0 c1 in
  assert (length c = length c0 + length c1);
  assert (length c = length m);
  let tg = Spec.Poly1305.poly1305_mac c mkey in
  (tg,c)

let secretbox_open_detached (k:key) (n:nonce) (tg:tag) (c:bytes{length c / size_block <= max_size_t}) : option (m:bytes{length m = length c}) =
  let (subkey,aekey) = secretbox_init k n in
  let n1 = sub n 16 8 in
  let mkey = sub aekey 0 32 in
  let ekey0 = sub aekey 32 32 in
  let tg' = Spec.Poly1305.poly1305_mac c mkey in
  if Lib.ByteSequence.lbytes_eq tg tg' then (
    let block0 = create 32 (u8 0) in
    let clen0 = if length c <= 32 then length c else 32 in
    let c0 = Seq.slice c 0 clen0 in
    let c1 = Seq.slice c clen0 (length c) in
    assert (length c1 / size_block <= length c / size_block);
    assert (clen0 <= 32);
    assert (length c0 + length c1 = length c);
    let block0 = update_sub block0 0 clen0 c0 in
    let block0 = map2 (^.) block0 ekey0 in
    let m0 = sub block0 0 clen0 in
    let m1 = Spec.Salsa20.salsa20_decrypt_bytes subkey n1 1 c1 in
    let m = Seq.append m0 m1 in
    assert (length m = length m0 + length m1);
    Some m)
  else None

let secretbox_easy (k:key) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : c:bytes{length c = size_tag + length m} =
  let (tg,c) = secretbox_detached k n m in
  Seq.append tg c

let secretbox_open_easy (k:key) (n:nonce) (c:bytes{length c >= size_tag /\ (length c - size_tag) / size_block <= max_size_t}) : option (m:bytes{length m = length c - size_tag}) =
  let tg = Seq.slice c 0 size_tag in
  let e = Seq.slice c size_tag (length c) in
  secretbox_open_detached k n tg e

