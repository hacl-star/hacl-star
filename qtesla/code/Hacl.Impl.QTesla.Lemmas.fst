module Hacl.Impl.QTesla.Lemmas

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.QTesla.Params

module UI32 = FStar.UInt32
module I64 = FStar.Int64

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val lemma_logand32_value_max: x:I64.t -> Lemma
  (ensures (I64.v I64.(x &^ 0xFFFFFFFFL) <= pow2 32 - 1))

let lemma_logand32_value_max _ = admit()

val lemma_logand32_value_min: x:I64.t -> Lemma
  (ensures (I64.v I64.(x &^ 0xFFFFFFFFL) >= 0))

let lemma_logand32_value_min _ = admit()

(*
val lemma_logand_value_max: x:I64.t -> n:nat -> Lemma
  (requires (n >= 2 /\ n <= 64 /\ FStar.Int.fits (pow2 n - 1) n))
  (ensures (I64.v I64.(x &^ (I64.int_to_t (pow2 n))) <= pow2 n - 1))
*)
