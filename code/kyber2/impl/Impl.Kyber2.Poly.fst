module Impl.Kyber2.Poly

open Spec.Kyber2.Params

open Impl.Kyber2.NumericTypes.MontgomeryInt16

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Impl.Kyber2.GroupMontgomery
open Spec.Kyber2.Reduce

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open Lib.NumericTypes

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

open Impl.Kyber2.FunctionInstantiation
open Impl.Kyber2.CBD

open FStar.Math.Lemmas

open Spec.Kyber2.Poly

module Buf = Lib.Buffer
module Seq = Lib.Sequence

assume val poly_compress: d:size_t{v d < 16 /\ pow2 (v d) < params_q}
 -> p:poly
 -> Stack unit
   (requires fun h -> live h p)
   (ensures fun h0 _ h1 -> modifies1 p h0 h1 /\ to_spec_poly h1 p == Spec.Kyber2.Poly.poly_compress (v d) (to_spec_poly h0 p))

assume val poly_decompress: d:size_t{v d < 16 /\ pow2 (v d) < params_q}
  -> p:poly
  -> Stack unit
    (requires fun h -> live h p /\ let sp = to_spec_poly h p in (forall (i:nat). {:pattern (index #_ #params_n sp i)} i < params_n ==> sint_v #S16 #SEC (index #_ #params_n sp i) < pow2 d))
    (ensures fun h -> modifies1 p h0 h1 /\ to_spec_poly h1 p == Spec.Kyber2.Poly.poly_decompress (v d) (to_spec_poly h0 p))

assume val vec_compress: d:size_t{v d < 16 /\ pow2 (v d) < params_q}
  -> v0:vec
  -> Stack unit
    (requires fun h -> live h v0)
    (ensures fun h0 _ h1 -> modifies1 v0 h0 h1 /\ to_spec_vec h1 v0 == Spec.Kyber2.Poly.vec_compress (v d) (to_spec_vec h0 v0))

assume val vec_decompress: d:size_t{v d < 16 /\ pow2 (v d) < params_q}
  -> v0:vec
  -> Stack unit
    (requires fun h -> live h v0 /\ let sv = to_spec_vec h v0 in (forall (i:nat{i<params_k}). forall (j:nat{j<params_n}). sint_v #S16 #SEC (index #_ #params_n (index #_ #params_k sv i) j) < pow2 d))
    (ensures fun h0 _ h1 -> modifies1 v0 h0 h1 /\ to_spec_vec h1 v0 == Spec.Kyber2.Poly.vec_compress (v d) (to_spec_vec h0 v0))
