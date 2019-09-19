module Hacl.Spec.Bignum.Convert

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Spec.Bignum

module S = Spec.RSAPSS


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


val bignum_from_bytes_f: len:size_nat{8 * len <= max_size_t} -> lseq uint8 (8 * len) -> i:nat{i < len} -> uint64
let bignum_from_bytes_f len b i =
  uint_from_bytes_be (sub b ((len - i - 1) * 8) 8)


val bignum_from_bytes_: len:size_nat{8 * len <= max_size_t} -> lseq uint8 (8 * len) -> lbignum len
let bignum_from_bytes_ len b = createi len (bignum_from_bytes_f len b)


val bignum_from_bytes: len:size_pos{8 * S.blocks len 8 <= max_size_t} -> lseq uint8 len -> lbignum (S.blocks len 8)
let bignum_from_bytes len b =
  let bnLen = S.blocks len 8 in
  let tmpLen = 8 * bnLen in
  let tmp = create tmpLen (u8 0) in
  let tmp = update_sub tmp (tmpLen - len) len b in
  bignum_from_bytes_ bnLen tmp


val bignum_to_bytes_f: len:size_nat{8 * len <= max_size_t} -> lbignum len -> i:nat{i < len} -> unit -> unit & lseq uint8 8
let bignum_to_bytes_f len b i () =
  (), uint_to_bytes_be b.[len - i - 1]


val bignum_to_bytes_: len:size_nat{8 * len <= max_size_t} -> lbignum len -> lseq uint8 (8 * len)
let bignum_to_bytes_ len b =
  let a_spec (i:nat{i <= len}) = unit in
  let _, o = generate_blocks 8 len len a_spec
    (bignum_to_bytes_f len b) () in
  o


val bignum_to_bytes: len:size_pos{8 * S.blocks len 8 <= max_size_t} -> lbignum (S.blocks len 8) -> lseq uint8 len
let bignum_to_bytes len b =
  let bnLen = S.blocks len 8 in
  let tmpLen = 8 * bnLen in
  let tmp = bignum_to_bytes_ bnLen b in
  sub tmp (tmpLen - len) len


val bignum_from_bytes_lemma: len:size_pos{8 * S.blocks len 8 <= max_size_t} -> b:lseq uint8 len -> Lemma
  (bn_v (bignum_from_bytes len b) == nat_from_bytes_be b)
let bignum_from_bytes_lemma len b = admit()


val bignum_to_bytes_lemma: len:size_pos{8 * S.blocks len 8 <= max_size_t} -> b:lbignum (S.blocks len 8){bn_v b < pow2 (8 * len)} -> Lemma
  (bignum_to_bytes len b == nat_to_bytes_be len (bn_v b))
let bignum_to_bytes_lemma len b = admit()
