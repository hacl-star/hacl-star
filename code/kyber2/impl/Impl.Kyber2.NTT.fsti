module Impl.Kyber2.NTT

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Impl.Kyber2.Group
open Impl.Kyber2.Ring
open Lib.Sequence
open Lib.Buffer

module ST = FStar.HyperStack.ST
module Buf = Lib.Buffer
module Seq = Lib.Sequence

open Spec.Kyber2.Params
open Impl.Kyber2.NumericTypes.MontgomeryInt16
open Lib.Arithmetic.Sums
module MGroup = Impl.Kyber2.GroupMontgomery
module Group = Impl.Kyber2.Group

open FStar.Math.Lemmas
open Lib.IntTypes

open Spec.Kyber2.NTT

assume val ntt:
  p:poly
  -> Stack unit
    (requires fun h -> live h p /\ (forall (x:size_nat{x<params_n}). v h.[|p|].[x] <= params_q /\ v h.[|p|].[x] >= - params_q)
    (ensures fun h0 _ h1 -> to_spec_poly h1 p == Spec.Kyber2.NTT.ntt (to_spec_poly h0 p))

assume val nttinv:
  p:poly
  -> Stack unit
    (requires fun h -> live h p /\ (forall (x:size_nat{x<params_n}). v h.[|p|].[x] <= params_q /\ v h.[|p|].[x] >= - params_q)
    (ensures fun h0 _ h1 -> to_spec_poly h1 p == Spec.Kyber2.NTT.nttinv (to_spec_poly h0 p))
