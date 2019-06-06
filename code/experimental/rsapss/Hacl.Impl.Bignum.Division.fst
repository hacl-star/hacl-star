module Hacl.Impl.Bignum.Division

open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Shift
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Multiplication
open Hacl.Impl.Bignum.Addition
open Hacl.Spec.Bignum


val bn_divide:
     #aLen:bn_len
  -> #bLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> res:lbignum aLen
  -> Stack unit
    (requires fun h ->
     live h a /\ live h b /\ all_disjoint [loc a; loc b; loc res] /\
     as_snat h b <> 0)
    (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_snat h1 res = as_snat h0 a / as_snat h0 b)
let bn_divide #aLen #bLen a b res = admit()
