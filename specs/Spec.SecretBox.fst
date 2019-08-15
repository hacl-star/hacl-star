module Spec.SecretBox

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

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

let get_len0 (len:nat) : r:size_nat{r <= 32} =
  if len <= 32 then len else 32

let secretbox_detached (k:key) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : (tag & c:bytes{length c = length m}) =
  let (subkey,aekey) = secretbox_init k n in
  let n1 = sub n 16 8 in
  let mkey = sub aekey 0 32 in
  let ekey0 = sub aekey 32 32 in

  let mlen0 = get_len0 (length m) in
  let m0 = Seq.slice m 0 mlen0 in
  let m1 = Seq.slice m mlen0 (length m) in

  let block0 = create 32 (u8 0) in
  let block0 = update_sub block0 0 mlen0 m0 in
  let block0 = map2 (^.) block0 ekey0 in

  let c0 = sub block0 0 mlen0 in
  let c1 = Spec.Salsa20.salsa20_encrypt_bytes subkey n1 1 m1 in
  let c = Seq.append c0 c1 in

  let tg = Spec.Poly1305.poly1305_mac c mkey in
  (tg, c)

let secretbox_open_detached (k:key) (n:nonce) (tg:tag) (c:bytes{length c / size_block <= max_size_t}) : option (m:bytes{length m = length c}) =
  let (subkey,aekey) = secretbox_init k n in
  let n1 = sub n 16 8 in
  let mkey = sub aekey 0 32 in
  let ekey0 = sub aekey 32 32 in

  let tg' = Spec.Poly1305.poly1305_mac c mkey in

  if Lib.ByteSequence.lbytes_eq tg tg' then (
    let clen0 = get_len0 (length c) in
    let c0 = Seq.slice c 0 clen0 in
    let c1 = Seq.slice c clen0 (length c) in

    let block0 = create 32 (u8 0) in
    let block0 = update_sub block0 0 clen0 c0 in
    let block0 = map2 (^.) block0 ekey0 in

    let m0 = sub block0 0 clen0 in
    let m1 = Spec.Salsa20.salsa20_decrypt_bytes subkey n1 1 c1 in
    let m = Seq.append m0 m1 in
    Some m)
  else None

let secretbox_easy (k:key) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : c:bytes{length c = size_tag + length m} =
  let (tg,c) = secretbox_detached k n m in
  Seq.append tg c

let secretbox_open_easy (k:key) (n:nonce) (c:bytes{length c >= size_tag /\ (length c - size_tag) / size_block <= max_size_t}) : option (m:bytes{length m = length c - size_tag}) =
  let tg = Seq.slice c 0 size_tag in
  let e = Seq.slice c size_tag (length c) in
  secretbox_open_detached k n tg e
