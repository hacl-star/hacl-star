module Hacl.Bignum.Lib

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Base
open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.Lib
module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Get and set i-th bit of a bignum
///

inline_for_extraction noextract
val bn_get_ith_bit:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_get_ith_bit (as_seq h0 b) (v i))

let bn_get_ith_bit len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  let tmp = input.(i) in
  (tmp >>. j) &. u64 1


inline_for_extraction noextract
val bn_set_ith_bit:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_set_ith_bit (as_seq h0 b) (v i))

let bn_set_ith_bit len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  input.(i) <- input.(i) |. (u64 1 <<. j)


inline_for_extraction noextract
val cswap2_st:
    len:size_t
  -> bit:uint64
  -> b1:lbuffer uint64 len
  -> b2:lbuffer uint64 len ->
  Stack unit
  (requires fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2)
  (ensures  fun h0 _ h1 -> modifies (loc b1 |+| loc b2) h0 h1 /\
    (as_seq h1 b1, as_seq h1 b2) == S.cswap2 bit (as_seq h0 b1) (as_seq h0 b2))

let cswap2_st len bit b1 b2 =
  [@inline_let]
  let mask = u64 0 -. bit in
  [@inline_let]
  let spec h0 = S.cswap2_f mask in

  let h0 = ST.get () in
  loop2 h0 len b1 b2 spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v len) (spec h0) (as_seq h0 b1, as_seq h0 b2) (v i);
    let dummy = mask &. (b1.(i) ^. b2.(i)) in
    b1.(i) <- b1.(i) ^. dummy;
    b2.(i) <- b2.(i) ^. dummy
  )
