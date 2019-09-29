module Hacl.Spec.Bignum.Convert

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Spec.Bignum


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_from_bytes_be_f: len:size_nat{8 * len <= max_size_t} -> lseq uint8 (8 * len) -> i:nat{i < len} -> uint64
let bn_from_bytes_be_f len b i =
  uint_from_bytes_be (sub b ((len - i - 1) * 8) 8)


val bn_from_bytes_be_: len:size_nat{8 * len <= max_size_t} -> lseq uint8 (8 * len) -> lbignum len
let bn_from_bytes_be_ len b = createi len (bn_from_bytes_be_f len b)


val bn_from_bytes_be: len:size_pos{8 * blocks len 8 <= max_size_t} -> lseq uint8 len -> lbignum (blocks len 8)
let bn_from_bytes_be len b =
  let bnLen = blocks len 8 in
  let tmpLen = 8 * bnLen in
  let tmp = create tmpLen (u8 0) in
  let tmp = update_sub tmp (tmpLen - len) len b in
  bn_from_bytes_be_ bnLen tmp


val bn_to_bytes_be_f: len:size_nat{8 * len <= max_size_t} -> lbignum len -> i:nat{i < len} -> unit -> unit & lseq uint8 8
let bn_to_bytes_be_f len b i () =
  (), uint_to_bytes_be b.[len - i - 1]


val bn_to_bytes_be_: len:size_nat{8 * len <= max_size_t} -> lbignum len -> lseq uint8 (8 * len)
let bn_to_bytes_be_ len b =
  let a_spec (i:nat{i <= len}) = unit in
  let _, o = generate_blocks 8 len len a_spec
    (bn_to_bytes_be_f len b) () in
  o


val bn_to_bytes_be: len:size_pos{8 * blocks len 8 <= max_size_t} -> lbignum (blocks len 8) -> lseq uint8 len
let bn_to_bytes_be len b =
  let bnLen = blocks len 8 in
  let tmpLen = 8 * bnLen in
  let tmp = bn_to_bytes_be_ bnLen b in
  sub tmp (tmpLen - len) len


val bn_from_bytes_be_lemma: len:size_pos{8 * blocks len 8 <= max_size_t} -> b:lseq uint8 len -> Lemma
  (bn_v (bn_from_bytes_be len b) == nat_from_bytes_be b)
let bn_from_bytes_be_lemma len b = admit()


val bn_to_bytes_be_lemma: len:size_pos{8 * blocks len 8 <= max_size_t} -> b:lbignum (blocks len 8){bn_v b < pow2 (8 * len)} -> Lemma
  (bn_to_bytes_be len b == nat_to_bytes_be len (bn_v b))
let bn_to_bytes_be_lemma len b = admit()
