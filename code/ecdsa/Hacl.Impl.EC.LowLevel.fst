module Hacl.Impl.EC.LowLevel

open Hacl.Bignum

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
(* open Hacl.EC.Lemmas *)

open Spec.ECC
open Spec.ECC.Curves

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon
(* 
open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P384.LowLevel
open Hacl.Impl.EC.Masking
 *)
open Lib.IntTypes.Intrinsics
(* open Hacl.Impl.EC.LowLevel.Lemmas *)


open Lib.Loops


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let mul #c f r out =
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  bn_mul len len f r out;
  Hacl.Spec.Bignum.bn_mul_lemma (as_seq h0 f) (as_seq h0 r)

let mul_p256 f r out = mul #P256 f r out