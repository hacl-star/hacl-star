module Hacl.Impl.QTesla.Lemmas

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open FStar.Int

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.QTesla.Params

module UI32 = FStar.UInt32
module UI64 = FStar.UInt64
module I32 = FStar.Int32
module I64 = FStar.Int64

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val my_logand_pos_le: #n:pos{1 < n} -> a:int_t n -> b:int_t n{0 <= b} ->
  Lemma (0 <= Int.logand a b /\ Int.logand a b <= b)
let my_logand_pos_le #n a b =
  UInt.logand_le (to_uint a) (to_uint b)

val lemma_logand32_value_max: x:UI64.t -> Lemma
//  (ensures (I64.v I64.(x &^ 0xFFFFFFFFL) <= pow2 32 - 1))
  (ensures UI64.v (UI64.logand x 0xFFFFFFFFuL) <= pow2 32 - 1)

let lemma_logand32_value_max x = 
    assert(UI64.v 0xFFFFFFFFuL == pow2 32 - 1);
    //sign_bit_positive #I64.n (I64.v (I64.logand x 0xFFFFFFFFL));
    //my_logand_pos_le (I64.v x) (I64.v 0xFFFFFFFFL)
    UInt.logand_le (UI64.v x) 0xFFFFFFFF

val lemma_logand32_value_min: x:UI64.t -> Lemma
  (ensures (UI64.v (UI64.logand x 0xFFFFFFFFuL) >= 0))

let lemma_logand32_value_min x = UInt.logand_le (UI64.v x) 0xFFFFFFFF

val shift_right_value_lemma_int64: x:I64.t{0 <= I64.v x} -> s:UI32.t{UI32.v s < UI64.n} -> Lemma
  (ensures I64.v (I64.shift_right x s) = (I64.v x) / pow2 (UI32.v s))

let shift_right_value_lemma_int64 x s =
  FStar.UInt.shift_right_value_lemma #UI64.n (I64.v x) (UI32.v s)

val shift_arithmetic_right_value_lemma_int64 : x:I64.t -> s:UI32.t {UI32.v s < UI64.n} -> Lemma
  (ensures I64.v (I64.shift_arithmetic_right x s) = (I64.v x) / pow2 (UI32.v s))

let shift_arithmetic_right_value_lemma_int64 x s = admit()
(*  if (I64.v x >= 0)
  then UInt.shift_right_value_lemma #UI64.n (I64.v x) (UI32.v s)
  else 
  begin
      UInt.shift_right_value_lemma #UI64.n -(I64.v x) (UI32.v s);
      assert(I64.v (I64.shift_arithmetic_right x s) == I64.v -(I64.shift_right (-x) s))
  end*)

val elem_product_fits_int64: x:elem_base -> y:elem_base -> GTot bool
let elem_product_fits_int64 x y = FStar.Int.fits (elem_v x * elem_v y) 64

// TODO (kkane): This lemma isn't actually true. We'll need to replace it where it is as we fix our proofs.
val lemma_elem_product_fits_int64: x:elem_base -> y:elem_base -> Lemma
  (ensures elem_product_fits_int64 x y /\ FStar.Int.fits (elem_v x * elem_v y * I64.v params_qinv) 64)

let lemma_elem_product_fits_int64 x y = admit()

//val lemma_int32_sar_n_minus_1: x:I32.t -> Lemma
//  (ensures (x >=^ 0l) <==> I32.(x >>^ (UI32.uint_to_t (I32.n - 1)) == 0l) /\
//           (x <^ 0l) <==> I32.(x >>^ (UI32.uint_to_t (I32.n - 1)) == (-1l)))
//  (ensures ((I32.v x >= 0) <==> I32.v I32.(x >>>^ (UI32.uint_to_t (I32.n - 1))) == 0) /\
//           ((I32.v x < 0) <==> I32.v I32.(x >>>^ (UI32.uint_to_t (I32.n - 1))) == (-1)))

//let lemma_int32_sar_n_minus_1 x = admit()// shift_arithmetic_right_lemma_1 #I32.n (I32.v x) (I32.n - 1) (I32.n - 1)

val lemma_int32_logxor_identities: x:I32.t -> Lemma
  (ensures I32.v (I32.logxor x 0l) == I32.v x /\
           I32.v (I32.logxor x (-1l)) == (-1) * (I32.v x) - 1)

let lemma_int32_logxor_identities x = 
    nth_lemma (Int.logxor (I32.v x) (Int.zero I32.n)) (I32.v x);
    assume(I32.v (I32.logxor x (-1l)) == (-1) * (I32.v x) - 1)

    
val lemma_int32_logor_zero: x:I32.t -> Lemma
  (ensures I32.logor x 0l == x /\ I32.logor 0l x == x)

let lemma_int32_logor_zero x = 
  nth_lemma #I32.n (I32.v (I32.logor x (I32.int_to_t (zero I32.n)))) (I32.v x);
  nth_lemma #I32.n (I32.v (I32.logor (I32.int_to_t (zero I32.n)) x)) (I32.v x)

val lemma_int32_lognot_zero: x:I32.t -> Lemma
  (ensures ((x == 0l) ==> (lognot x == (-1l))) /\
           ((x == (-1l)) ==> (lognot x == 0l)))

let lemma_int32_lognot_zero x = 
    nth_lemma (Int.lognot (Int.zero I32.n)) (Int.ones I32.n);
    nth_lemma (Int.lognot (Int.ones I32.n)) (Int.zero I32.n)

open FStar.UInt

val uint_pow2_minus_one: m:nat{m <= bits U32} -> Tot uint32
let uint_pow2_minus_one m =
  FStar.Math.Lemmas.pow2_le_compat (bits U32) m;
  u32 (pow2 m - 1)

val uint_logand_pow2_minus_one: a:uint32 -> m:pos{m <= bits U32} ->
  Lemma (0 <= v (Lib.IntTypes.logand a (uint_pow2_minus_one m)) /\
    v (Lib.IntTypes.logand a (uint_pow2_minus_one m)) <= v (uint_pow2_minus_one m))
let uint_logand_pow2_minus_one a m = admit()
  //UInt.logand_le #(numbytes U32) (v a) (v (uint_pow2_minus_one m))

val lemma_shift_left_one_eq_pow2: s:shiftval U32 -> Lemma
  (ensures v (Lib.IntTypes.shift_left (u32 1) s) == pow2 (v s))

let lemma_shift_left_one_eq_pow2 s = admit()
(*
val lemma_logand_value_max: x:I64.t -> n:nat -> Lemma
  (requires (n >= 2 /\ n <= 64 /\ FStar.Int.fits (pow2 n - 1) n))
  (ensures (I64.v I64.(x &^ (I64.int_to_t (pow2 n))) <= pow2 n - 1))
*)

(*private let lemma_q_log_fact _ : Lemma (ensures pow2 (v params_q_log) < 2 * elem_v params_q) =
    assert_norm(pow2 (v params_q_log) < 2 * elem_v params_q)*)
