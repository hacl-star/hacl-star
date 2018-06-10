module Hacl.Impl.Lemmas

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.Buffer.Lemmas
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Spec = Spec.Blake2s



///
/// Helper lemmata
///

val lemma_cast_to_u64: x:uint32 -> Lemma
  (requires (True))
  (ensures  (to_u64 #U32 x == u64 (uint_v #U32 x)))
  [SMTPat (to_u64 #U32 x)]

let lemma_cast_to_u64 x = admit()

val lemma_modifies0_is_modifies1: #a0:Type -> #len0:size_nat -> b0:lbuffer a0 len0 -> h0:mem -> h1:mem -> Lemma
  (requires (True))
  (ensures  (h0 == h1 ==> modifies1 b0 h0 h1))
let lemma_modifies0_is_modifies1 #a0 #len0 b0 h0 h1 = admit()


val lemma_modifies0_is_modifies2: #a0:Type -> #a1:Type -> #len0:size_nat -> #len1:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> h0:mem -> h1:mem -> Lemma
  (requires (True))
  (ensures  (h0 == h1 ==> modifies2 b0 b1 h0 h1))
let lemma_modifies0_is_modifies2 #a0 #a1 #len0 #len1 b0 b1 h0 h1 = admit()


val lemma_modifies1_is_modifies2: #a0:Type -> #a1:Type -> #len0:size_nat -> #len1:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> h0:mem -> h1:mem -> Lemma
  (requires (True))
  (ensures  (modifies1 b0 h0 h1 ==> modifies2 b0 b1 h0 h1))
let lemma_modifies1_is_modifies2 #a0 #a1 #len0 #len1 b0 b1 h0 h1 = admit()


val lemma_repeati: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> i:size_nat{i < n} -> Lemma
  (requires True)
  (ensures  (f i (repeati #a i f init) == repeati #a (i + 1) f init))

let lemma_repeati #a n f init i = admit()


val lemma_repeati_zero: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> Lemma
  (requires True)
  (ensures  (init == repeati #a 0 f init))

let lemma_repeati_zero #a n f init = admit()


(* val lemma_size_to_uint32_equal_u32_of_v_of_size_t: x:size_t -> Lemma *)
(*   (requires True) *)
(*   (ensures (size_to_uint32 x == u32 (v x))) *)
(*   [SMTPat (u32 (v x))] *)
(* let lemma_size_to_uint32_equal_u32_of_v_of_size_t x = admit() *)


val lemma_value_mixed_size_addition: x:size_t -> y:size_nat -> Lemma
  (requires True)
  (ensures (v (x +. (size y)) == v x + y))
  [SMTPat (v (x +. (size y)) == v x + y)]
let lemma_value_mixed_size_addition x y = admit()

(* val lemma_modifies2_of_subs_is_modifies1: #h0:mem -> #h1:mem -> #a:Type0 -> #len:size_nat -> #pos0:size_nat -> #len0:size_nat{pos0 + len0 < len} -> #pos1:size_nat -> #len1:size_nat{pos1 + len1 <= len} -> buf:lbuffer a len -> sub0:lbuffer a len0 -> sub1:lbuffer a len1 -> *)
(*   Lemma *)
(*     (requires (True)) *)
(*     (ensures  ((modifies2 sub0 sub1 h0 h1 *)
(*                /\ sub0 == sub buf (size pos0) (size len0) *)
(*                /\ sub1 == sub buf (size pos1) (size len1)) ==> modifies1 buf h0 h1)) *)

(* let lemma_modifies2_of_subs_is_modifies1 #h0 #h1 #a #len #pos0 #len0 #pos1 #len1 buf sub0 sub1 = admit() *)

val lemma_modifies2_trans: #h0:mem -> #h1:mem -> #h2:mem -> #a0:Type0 -> #a1:Type0 -> #len0:size_nat -> #len1:size_nat -> buf0:lbuffer a0 len0 -> buf1:lbuffer a1 len1 ->
  Lemma
    (requires (modifies2 buf0 buf1 h0 h1 /\ modifies2 buf0 buf1 h1 h2))
    (ensures  (modifies2 buf0 buf1 h0 h2))

let lemma_modifies2_trans #h0 #h1 #h2 #a0 #a1 #len0 #len1 buf0 buf1 = admit()
