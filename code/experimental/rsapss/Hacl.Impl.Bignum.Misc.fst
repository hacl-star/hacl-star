module Hacl.Impl.Bignum.Misc

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Bignum.Core
open Hacl.Spec.Bignum

val bn_assign_uint64:
     #len:bn_len
  -> a:lbignum len
  -> x:uint64
  -> Stack unit
    (requires fun h -> live h a)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1 /\ as_snat h1 a = v x)
let bn_assign_uint64 #len a x =
  a.(0ul) <- x;
  if len >. 1ul then memset (sub a 1ul (len -! 1ul)) (uint 0) (len -! 1ul);
  let h = FStar.HyperStack.ST.get () in
  assume (as_snat h a = v x)
