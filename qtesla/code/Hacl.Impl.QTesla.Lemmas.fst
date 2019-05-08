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
module I32 = FStar.Int32
module I64 = FStar.Int64

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val lemma_logand32_value_max: x:I64.t -> Lemma
  (ensures (I64.v I64.(x &^ 0xFFFFFFFFL) <= pow2 32 - 1))

let lemma_logand32_value_max _ = admit()

val lemma_logand32_value_min: x:I64.t -> Lemma
  (ensures (I64.v I64.(x &^ 0xFFFFFFFFL) >= 0))

let lemma_logand32_value_min _ = admit()

val elem_product_fits_int64: x:elem_base -> y:elem_base -> GTot bool
let elem_product_fits_int64 x y = FStar.Int.fits (elem_v x * elem_v y) 64

val lemma_elem_product_fits_int64: x:elem_base -> y:elem_base -> Lemma
  (ensures elem_product_fits_int64 x y /\ FStar.Int.fits (elem_v x * elem_v y * I64.v params_qinv) 64)

let lemma_elem_product_fits_int64 x y = admit()

val lemma_int32_sar_n_minus_1: x:I32.t -> Lemma
//  (ensures (x >=^ 0l) <==> I32.(x >>^ (UI32.uint_to_t (I32.n - 1)) == 0l) /\
//           (x <^ 0l) <==> I32.(x >>^ (UI32.uint_to_t (I32.n - 1)) == (-1l)))
  (ensures ((I32.v x >= 0) <==> I32.v I32.(x >>^ (UI32.uint_to_t (I32.n - 1))) == 0) /\
           ((I32.v x < 0) <==> I32.v I32.(x >>^ (UI32.uint_to_t (I32.n - 1))) == (-1)))

let lemma_int32_sar_n_minus_1 x = admit()

val lemma_int32_bitwise_or: x:I32.t -> Lemma
  (ensures I32.v (0l ^^ x) == I32.v x /\
           I32.v ((-1l) ^^ x) == (-1) * I32.v x - 1)

let lemma_int32_bitwise_or x = admit()

(*
val lemma_logand_value_max: x:I64.t -> n:nat -> Lemma
  (requires (n >= 2 /\ n <= 64 /\ FStar.Int.fits (pow2 n - 1) n))
  (ensures (I64.v I64.(x &^ (I64.int_to_t (pow2 n))) <= pow2 n - 1))
*)
