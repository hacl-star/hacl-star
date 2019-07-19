module Impl.Kyber2.Arithmetic.Sums

open Lib.IntTypes
open Lib.Buffer

module Group = Impl.Kyber2.Group
module MGroup = Impl.Kyber2.GroupMontgomery

//open FStar.Tactics.Typeclasses
open FStar.HyperStack.All
open FStar.Mul

open Kyber2.Params

module Buf = Lib.Buffer
module Seq = Lib.Sequence

inline_for_extraction
val sum_n:
  #n:size_t
  -> l:lbuffer (Group.t) n
  -> output:lbuffer (Group.t) (size 1)
  -> Stack unit (requires fun h -> live h l /\ live h output /\ Buf.disjoint l output) (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ Seq.index h1.[|output|] 0 == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t h0.[|l|])

inline_for_extraction
val sum_n_montgomery:
  #n:size_t
  -> l:lbuffer (MGroup.montgomery_t) n
  -> output:lbuffer (MGroup.montgomery_t) (size 1)
  -> Stack unit (requires fun h -> live h l /\ live h output /\ Buf.disjoint l output) (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ MGroup.to_t (Seq.index h1.[|output|] 0) == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.map MGroup.to_t h0.[|l|]))

inline_for_extraction
val sum_n_montgomery_no_plus_m:
  #n:size_t{v n < pow2 (params_logr-1)}
  -> l:lbuffer (MGroup.montgomery_t) n
  -> output:lbuffer (x:int32{- params_q * pow2 (params_logr-1) <= sint_v x /\ sint_v x < params_q * pow2 (params_logr -1)}) (size 1)
  -> Stack unit (requires fun h -> live h l /\ live h output /\ Buf.disjoint l output ) (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ (sint_v (Seq.index h1.[|output|] 0) >= - (v n) * params_q /\ sint_v (Seq.index h1.[|output|] 0) <= (v n) * params_q) /\ MGroup.int32_to_t (Seq.index h1.[|output|] 0) == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.map MGroup.to_t h0.[|l|]))

inline_for_extraction
val sum_n_cbd:
  l: lbuffer uint1 (size params_eta)
  -> output:lbuffer int16 (size 1)
  -> Stack unit (requires fun h -> live h l /\ live h output /\ Buf.disjoint l output) (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ v (Seq.index h1.[|output|] 0) >= 0 /\ v (Seq.index h1.[|output|] 0) <= params_eta /\ Group.int16_to_t (Seq.index h1.[|output|] 0) == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.map Group.int16_to_t (Seq.map to_i16 (h0.[|l|]))))
