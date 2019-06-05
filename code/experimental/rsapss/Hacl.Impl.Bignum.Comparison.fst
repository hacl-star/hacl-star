module Hacl.Impl.Bignum.Comparison

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Core
open Hacl.Spec.Bignum


val max': a:size_t -> b:size_t -> size_t
let max' a b = if a >=. b then a else b

val bn_compare_generic:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> finval:bool
  -> i:size_t
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 _ h1 -> modifies loc_none h0 h1 /\ h0 == h1)
let rec bn_compare_generic #aLen #bLen a b finval i =
  if i =. 0ul then finval else begin
    let i = i -. size 1 in
    let t1 = bval aLen a i in
    let t2 = bval bLen b i in
    (if not (eq_u64 t1 t2) then
      if lt_u64 t1 t2 then true else false
    else bn_compare_generic a b finval i)
  end

inline_for_extraction
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
let bn_is_less #aLen #bLen a b =
  let res = bn_compare_generic a b false (max' aLen bLen) in
  let h = FStar.HyperStack.ST.get () in
  assume (res == (as_snat h a < as_snat h b));
  res

inline_for_extraction
val bn_is_leq:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 ->
     modifies loc_none h0 h1 /\ h0 == h1 /\
     r == (as_snat h0 a <= as_snat h0 b))
let bn_is_leq #aLen #bLen a b =
  let res = bn_compare_generic a b true (max' aLen bLen) in
  let h = FStar.HyperStack.ST.get () in
  assume (res == (as_snat h a <= as_snat h b));
  res

val bn_is_equal_:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:size_t
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 _ h1 -> modifies loc_none h0 h1 /\ h0 == h1)
let rec bn_is_equal_ #aLen #bLen a b i =
  if i >. 0ul then
    let i = i -. size 1 in
    let t1 = bval aLen a i in
    let t2 = bval bLen b i in
    (if not (eq_u64 t1 t2) then false else bn_is_equal_ a b i)
  else true

// This is straightforward copy of bn_is_less. There must be a better
// way to compare buffers.
val bn_is_equal:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 ->
     h0 == h1 /\ r == (as_snat h0 a = as_snat h0 b))
let bn_is_equal #aLen #bLen a b =
  let res = bn_is_equal_ a b (max' aLen bLen) in
  let h = FStar.HyperStack.ST.get () in
  assume (res == (as_snat h a = as_snat h b));
  res

inline_for_extraction
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
let bn_is_greater #aLen #bLen a b = bn_is_less b a

inline_for_extraction
val bn_is_geq:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 ->
     modifies loc_none h0 h1 /\ h0 == h1 /\
     r == (as_snat h0 a >= as_snat h0 b))
let bn_is_geq #aLen #bLen a b = bn_is_leq b a


val bn_is_zero_:
     #aLen:bn_len
  -> a:lbignum aLen
  -> i:size_t{v i <= v aLen}
  -> Stack bool
    (requires fun h -> live h a)
    (ensures  fun h0 _ h1 -> h0 == h1)
let rec bn_is_zero_ #aLen a i =
  if i =. 0ul then true else begin
    let i = i -. 1ul in
    if not (eq_u64 (a.(i)) (uint 0)) then false
    else bn_is_zero_ a i
  end

val bn_is_zero:
     #aLen:bn_len
  -> a:lbignum aLen
  -> Stack bool
    (requires fun h -> live h a)
    (ensures fun h0 r h1 ->
     h0 == h1 /\ r == (as_snat h0 a = 0))
let bn_is_zero #aLen a =
  let res = bn_is_zero_ a aLen in
  let h = FStar.HyperStack.ST.get () in
  assume (res == (as_snat h a = 0));
  res
