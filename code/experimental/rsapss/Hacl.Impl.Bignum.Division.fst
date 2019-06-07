module Hacl.Impl.Bignum.Division

open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Bignum.Addition
open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Misc
open Hacl.Spec.Bignum


// Naive binary non constant-time division. To be improved later.
// It's inspired by the boringssl, should I add the copyright notice?


// Sets a to (a mod m), where a < 2 * m. Returns (-1) if reduction was
// performed (a >= m), otherwise 0.
// a may have an additional word specified by carry.
val bn_reduce_once_in_place:
     #nLen:bn_len
  -> a:lbignum nLen
  -> carry:uint64
  -> m:lbignum nLen
  -> tmp:lbignum nLen
  -> Stack uint64
    (requires fun h ->
     live h a /\ live h m /\ live h tmp /\
     all_disjoint [loc a; loc m; loc tmp])
    (ensures fun h0 _ h1 -> modifies2 a tmp h0 h1)
let bn_reduce_once_in_place #nLen a carry m tmp =
  let carry2 = bn_sub a m tmp in
  let carry' = carry -. carry2 in
  if eq_u64 carry' (uint 0) then copy a tmp;
  carry'

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val bn_divide:
     #aLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> q:lbignum aLen
  -> r:lbignum aLen
  -> Stack unit
    (requires fun h ->
     live h a /\ live h b /\ live h q /\ live h r /\
     all_disjoint [loc a; loc b; loc q; loc r] /\
     as_snat h b <> 0)
    (ensures fun h0 _ h1 -> modifies2 q r h0 h1 /\
      as_snat h1 q = as_snat h0 a / as_snat h0 b /\
      as_snat h1 r = as_snat h0 a % as_snat h0 b)
let bn_divide #aLen a b q r =
  push_frame ();

  let tmp = create aLen (u64 0) in
  bn_assign_uint64 q (uint 0);
  bn_assign_uint64 r (uint 0);

  let h0 = FStar.HyperStack.ST.get () in
  let inv1 h i = modifies3 q r tmp h0 h in
  let inv2 h i = modifies3 q r tmp h0 h in

  Lib.Loops.for_rev aLen 0ul inv1 (fun i ->
    Lib.Loops.for_rev 64ul 0ul inv2 (fun bit ->
      let carry = bn_add r r r in
      r.(0ul) <- r.(0ul) |. ((a.(i) >>. bit) &. (u64 1));
      let subtracted = bn_reduce_once_in_place r carry b tmp in
      q.(i) <- q.(i) |. (((~. subtracted) &. (u64 1)) <<. bit)
  ));

  let h = FStar.HyperStack.ST.get () in

  assume (as_snat h q = as_snat h0 a / as_snat h0 b /\
          as_snat h r = as_snat h0 a % as_snat h0 b);

  pop_frame ()
