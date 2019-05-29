module Hacl.Impl.Bignum.Comparison

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Core

val bn_is_less_:
     #aLen:bn_len
  -> #bLen:bn_len{v bLen <= v aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:size_t{v i <= v aLen}
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 _ h1 -> modifies loc_none h0 h1 /\ h0 == h1)
let rec bn_is_less_ #aLen #bLen a b i =
  if i >. 0ul then
    let i = i -. size 1 in
    let t1 = a.(i) in
    let t2 = bval bLen b i in
    (if not (eq_u64 t1 t2) then
      if lt_u64 t1 t2 then true else false
    else bn_is_less_ a b i)
  else false

val bn_is_less:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 ->
     modifies loc_none h0 h1 /\ h0 == h1 /\
     r == (as_snat h0 a < as_snat h0 b))
[@"c_inline"]
let bn_is_less #aLen #bLen a b =
    let res =
      if bLen <=. aLen
      then (assert (v bLen <= v aLen); bn_is_less_ #aLen #bLen a b aLen)
      else (let res = bn_is_less_ #bLen #aLen b a bLen in not res) in
    admit();
    res

val bn_is_equal_:
     #aLen:bn_len
  -> #bLen:bn_len{v bLen <= v aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:size_t{v i <= v aLen}
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 _ h1 -> modifies loc_none h0 h1 /\ h0 == h1)
let rec bn_is_equal_ #aLen #bLen a b i =
  if i >. 0ul then
    let i = i -. size 1 in
    let t1 = a.(i) in
    let t2 = bval bLen b i in
    (if not (eq_u64 t1 t2) then false else bn_is_equal_ a b i)
  else true

// This is straightforward copy of bn_is_less. There must be a better
// way to compare buffers.
val bn_is_equal:
     #aLen:bn_len
  -> #bLen:bn_len{v bLen <= v aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 ->
     modifies loc_none h0 h1 /\ h0 == h1 /\
     r == (as_snat h0 a = as_snat h0 b))
let bn_is_equal #aLen #bLen a b = let res = bn_is_equal_ a b aLen in admit(); res

val bn_is_greater:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 ->
     modifies loc_none h0 h1 /\ h0 == h1 /\
     r == (as_snat h0 a > as_snat h0 b))
[@"c_inline"]
let bn_is_greater #aLen #bLen a b = bn_is_less b a
