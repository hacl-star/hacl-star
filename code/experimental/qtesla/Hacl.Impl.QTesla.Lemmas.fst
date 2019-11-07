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
module UI64 = FStar.UInt64
module I32 = FStar.Int32
module I64 = FStar.Int64

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val my_logand_pos_le: #n:pos{1 < n} -> a:Int.int_t n -> b:Int.int_t n{0 <= b} ->
  Lemma (0 <= Int.logand a b /\ Int.logand a b <= b)
let my_logand_pos_le #n a b =
  UInt.logand_le (Int.to_uint a) (Int.to_uint b)

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

val elem_product_fits_int64: x:elem_base -> y:elem_base -> GTot bool
let elem_product_fits_int64 x y = FStar.Int.fits (elem_v x * elem_v y) I64.n

val lemma_int32_logxor_identities: x:I32.t{I32.v x > Int.min_int I32.n} -> Lemma
  (ensures I32.v (I32.logxor x 0l) = I32.v x /\
           I32.v (I32.logxor x (-1l)) = (-1) * (I32.v x) - 1)

let lemma_int32_logxor_identities x = 
    let x = I32.v x in
    Int.nth_lemma (Int.logxor x (Int.zero I32.n)) x;
    if (x < 0) then
     begin
      Int.lognot_negative #I32.n x;
      UInt.lemma_lognot_value_mod #I32.n (x + pow2 I32.n)
     end
    else UInt.lemma_lognot_value_mod #I32.n x;
    Int.nth_lemma (Int.logxor x (Int.ones I32.n)) ((-x) - 1)
    
val lemma_int32_logor_zero: x:I32.t -> Lemma
  (ensures I32.logor x 0l == x /\ I32.logor 0l x == x)

let lemma_int32_logor_zero x = 
  Int.nth_lemma #I32.n (I32.v (I32.logor x (I32.int_to_t (Int.zero I32.n)))) (I32.v x);
  Int.nth_lemma #I32.n (I32.v (I32.logor (I32.int_to_t (Int.zero I32.n)) x)) (I32.v x)

val lemma_int32_lognot_zero: x:I32.t -> Lemma
  (ensures ((x == 0l) ==> (lognot x == (-1l))) /\
           ((x == (-1l)) ==> (lognot x == 0l)))

let lemma_int32_lognot_zero x = 
    Int.nth_lemma (Int.lognot (Int.zero I32.n)) (Int.ones I32.n);
    Int.nth_lemma (Int.lognot (Int.ones I32.n)) (Int.zero I32.n)

open FStar.UInt

val uint_pow2_minus_one: m:nat{m <= bits U32} -> Tot uint32
let uint_pow2_minus_one m =
  FStar.Math.Lemmas.pow2_le_compat (bits U32) m;
  u32 (pow2 m - 1)

val uint_logand_pow2_minus_one: a:uint32 -> m:pos{m <= bits U32} ->
  Lemma (0 <= v (Lib.IntTypes.logand a (uint_pow2_minus_one m)) /\
    v (Lib.IntTypes.logand a (uint_pow2_minus_one m)) <= v (uint_pow2_minus_one m))
let uint_logand_pow2_minus_one a m = 
  Lib.IntTypes.logand_le a (uint_pow2_minus_one m)

val lemma_shift_left_one_eq_pow2: s:shiftval U32 -> Lemma
  (ensures v (Lib.IntTypes.shift_left (u32 1) s) == pow2 (v s))

let lemma_shift_left_one_eq_pow2 s = 
  Lib.IntTypes.shift_left_lemma (u32 1) s;
  Math.Lemmas.pow2_lt_compat 32 (v s)

val lemma_mask_logor: a:I32.t -> b:I32.t -> mask:I32.t{I32.v mask == 0 \/ I32.v mask == (-1)} -> r:I32.t -> Lemma
    (requires r == I32.logor (I32.logand a mask) (I32.logand b (I32.lognot mask)))
    (ensures ((I32.v mask = 0) ==> (b == r)) /\ ((I32.v mask = (-1)) ==> (a == r)))

let lemma_mask_logor a b mask r =
    if I32.v mask = 0 then
      begin
      Int.nth_lemma #I32.n (I32.v mask) (Int.zero I32.n);
      Int.nth_lemma #I32.n (I32.v (I32.lognot mask)) (Int.ones I32.n);
      Int.logand_lemma_1 #I32.n (I32.v a);
      Int.logand_lemma_2 #I32.n (I32.v b);
      lemma_int32_logor_zero b
      end
    else 
      begin 
      Int.nth_lemma #I32.n (I32.v mask) (Int.ones I32.n);
      Int.nth_lemma #I32.n (I32.v (I32.lognot mask)) (Int.zero I32.n);
      Int.logand_lemma_1 #I32.n (I32.v b);
      Int.logand_lemma_2 #I32.n (I32.v a);
      lemma_int32_logor_zero a
      end

// Proofs for shift_right wholesale ripped off from HACL*'s Lib.IntTypes. I'm not sure why these
// lemmas aren't in ulib, or why HACL*'s shift_right doesn't make some statement about its behavior conforming to
// the ulib versions.
private val shift_right_value_aux_1: #n:pos{1 < n} -> a:Int.int_t n -> s:nat{n <= s} ->
  Lemma (Int.shift_arithmetic_right #n a s = a / pow2 s)
let shift_right_value_aux_1 #n a s =
  Math.Lemmas.pow2_le_compat s n;
  if a >= 0 then Int.sign_bit_positive a else Int.sign_bit_negative a

private val shift_right_value_aux_2: #n:pos{1 < n} -> a:Int.int_t n ->
  Lemma (Int.shift_arithmetic_right #n a 1 = a / 2)
let shift_right_value_aux_2 #n a =
  if a >= 0 then
    begin
    Int.sign_bit_positive a;
    UInt.shift_right_value_aux_3 #n a 1
    end
  else
    begin
    Int.sign_bit_negative a;
    let a1 = Int.to_vec a in
    let au = Int.to_uint a in
    let sar = Int.shift_arithmetic_right #n a 1 in
    let sar1 = Int.to_vec sar in
    let sr = UInt.shift_right #n au 1 in
    let sr1 = UInt.to_vec sr in
    assert (Seq.equal (Seq.slice sar1 1 n) (Seq.slice sr1 1 n));
    assert (Seq.equal sar1 (Seq.append (BitVector.ones_vec #1) (Seq.slice sr1 1 n)));
    UInt.append_lemma #1 #(n-1) (BitVector.ones_vec #1) (Seq.slice sr1 1 n);
    assert (Seq.equal (Seq.slice a1 0 (n-1)) (Seq.slice sar1 1 n));
    UInt.slice_left_lemma a1 (n-1);
    assert (sar + pow2 n = pow2 (n-1) + (au / 2));
    Math.Lemmas.pow2_double_sum (n-1);
    assert (sar + pow2 (n-1) = (a + pow2 n) / 2);
    Math.Lemmas.pow2_double_mult (n-1);
    Math.Lemmas.lemma_div_plus a (pow2 (n-1)) 2;
    assert (sar = a / 2)
  end

private val shift_right_value_aux_3: #n:pos -> a:Int.int_t n -> s:pos{s < n} ->
  Lemma (ensures Int.shift_arithmetic_right #n a s = a / pow2 s)
        (decreases s)
let rec shift_right_value_aux_3 #n a s =
  if s = 1 then
    shift_right_value_aux_2 #n a
  else
    begin
    let a1 = Int.to_vec a in
    assert (Seq.equal (BitVector.shift_arithmetic_right_vec #n a1 s)
                      (BitVector.shift_arithmetic_right_vec #n
                         (BitVector.shift_arithmetic_right_vec #n a1 (s-1)) 1));
    assert (Int.shift_arithmetic_right #n a s =
            Int.shift_arithmetic_right #n (Int.shift_arithmetic_right #n a (s-1)
) 1);
    shift_right_value_aux_3 #n a (s-1);
    shift_right_value_aux_2 #n (Int.shift_arithmetic_right #n a (s-1));
    assert (Int.shift_arithmetic_right #n a s = (a / pow2 (s-1)) / 2);
    Math.Lemmas.pow2_double_mult (s-1);
    Math.Lemmas.division_multiplication_lemma a (pow2 (s-1)) 2
    end

val shift_arithmetic_right_lemma_i32:
    a:I32.t
  -> b:UI32.t{UI32.v b > 0 /\ UI32.v b < I32.n}
  -> Lemma (I32.v (I32.shift_arithmetic_right a b) = I32.v a / pow2 (UI32.v b))

let shift_arithmetic_right_lemma_i32 a b =
    shift_right_value_aux_3 #I32.n (I32.v a) (UI32.v b)

val shift_arithmetic_right_lemma_i64:
    a:I64.t
  -> b:UI32.t{UI32.v b > 0 /\ UI32.v b < I64.n}
  -> Lemma (I64.v (I64.shift_arithmetic_right a b) = I64.v a / pow2 (UI32.v b))

let shift_arithmetic_right_lemma_i64 a b =
   shift_right_value_aux_3 #I64.n (I64.v a) (UI32.v b)

#push-options "--z3cliopt 'smt.arith.nl=false'"
// Generously borrowed from Vale.
val lemma_mul_nat_bound (a a' b b':nat) : Lemma
  (requires a <= a' /\ b <= b')
  (ensures 0 <= a * b /\ a * b <= a' * b')
  
let lemma_mul_nat_bound a a' b b' =
  let open FStar.Math.Lemmas in
  nat_times_nat_is_nat a b;
  lemma_mult_le_left a b b'; // a * b <= a * b'
  lemma_mult_le_right b' a a'; // a * b' <= a' * b'
  ()
#pop-options
