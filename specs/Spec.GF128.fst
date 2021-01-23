module Spec.GF128

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.GaloisField

//GF128 Field: to load bits in little-endian order set the parameters as follows
//let irred = u128 0x87
//let load_elem (b:lbytes 16) : elem = load_felem_le #gf128 b
//let store_elem (e:elem) : lbytes 16 = store_felem_le #gf128 e
//and use `fmul` instead of `fmul_be`

let irred = mk_int #U128 #SEC 0xE1000000000000000000000000000000
let gf128 = gf U128 irred
let elem = felem gf128
let load_elem (b:lbytes 16) : elem = load_felem_be #gf128 b
let store_elem (e:elem) : lbytes 16 = store_felem_be #gf128 e

(* GCM types and specs *)
let size_block : size_nat = 16
let size_key   : size_nat = 16

type block = lbytes size_block
type tag   = lbytes size_block
type key   = lbytes size_key

/// Specification

let encode (w:lbytes size_block) : Tot elem = load_elem w

let encode_last (len:size_nat{len < size_block}) (w:lbytes len) : Tot elem =
  let b = create size_block (u8 0) in
  let b = update_slice b 0 len w  in
  load_elem b

let decode (e:elem) : Tot block = store_elem e

let gf128_init (h:lbytes size_block) : Tot (elem & elem) =
  let r = load_elem h in
  zero, r

let gf128_update1 (r:elem) (b:lbytes size_block) (acc:elem) : Tot elem =
  (acc `fadd` encode b) `fmul_be` r

let gf128_finish (s:key) (acc:elem) : Tot tag =
  decode (acc `fadd` load_elem s)

let gf128_update_last (r:elem) (l:size_nat{l < size_block}) (b:lbytes l) (acc:elem) =
  if l = 0 then acc else (acc `fadd` encode_last l b) `fmul_be` r

let gf128_update (text:bytes) (acc:elem) (r:elem) : Tot elem =
  repeat_blocks #uint8 #elem size_block text
    (gf128_update1 r)
    (gf128_update_last r)
  acc

let gmul (text:bytes) (h:lbytes size_block) : Tot tag =
  let acc, r = gf128_init h in
  let acc = gf128_update text acc r in
  decode acc

let gmac (text:bytes) (h:lbytes size_block) (k:key) : Tot tag =
  let acc, r = gf128_init h in
  let acc = gf128_update text acc r in
  gf128_finish k acc
