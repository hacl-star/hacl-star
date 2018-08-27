module MPFR.Mul_1.Lemma
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64
open FStar.Int.Cast
open FStar.Mul
open MPFR.Lib
open MPFR.Lib.Spec
open MPFR.Mul.Spec
open MPFR.Round.Spec
open MPFR.Umul_ppmm
open MPFR.Dyadic
open MPFR.Maths

module I64 = FStar.Int64
module I32 = FStar.Int32
module U32 = FStar.UInt32

#set-options "--z3refresh --z3rlimit 100 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

val mpfr_mul_1_value_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct -> Lemma
    (requires ())
    (ensures  (
    let p = a.mpfr_prec in
    let r = mul_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let r = high_mant r (U32.v p) in
    let b0 = Seq.index (as_seq h b.mpfr_d) 0 in
    let c0 = Seq.index (as_seq h c.mpfr_d) 0 in
    let sh = U32.(gmp_NUMB_BITS -^ p) in
    let mask = mpfr_LIMB_MASK sh in
    let ax = I32.(b.mpfr_exp +^ c.mpfr_exp) in
    let a0, sb = umul_ppmm b0 c0 in
    let ax, a0 = if a0 <^ mpfr_LIMB_HIGHBIT
             then I32.(ax -^ 1l), (a0 <<^ 1ul) |^ (sb >>^ U32.(gmp_NUMB_BITS -^ 1ul))
             else ax, a0 in
    let a0 = a0 &^ (lognot mask) in
    v a0 * pow2 (r.len - 64) = r.limb /\ I32.v bx = r.exp /\
    v a0 >= pow2 63 /\ v a0 % pow2 (64 - p) = 0))
