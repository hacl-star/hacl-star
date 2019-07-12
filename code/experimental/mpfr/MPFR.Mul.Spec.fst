module MPFR.Mul.Spec

open FStar.Mul
open MPFR.Dyadic
open MPFR.Lib.Spec
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 15 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* In this specification we only consider MPFR normal numbers as input *)
val mul_limb: a:mpfr_reg_fp -> b:mpfr_reg_fp ->
    Tot (rm:nat{rm = (eval_abs a *. eval_abs b).significand /\
              rm % pow2 (a.len - a.prec + b.len - b.prec) = 0})

let mul_limb a b =
    lemma_pow2_mod_product_zero a.limb b.limb (a.len - a.prec) (b.len - b.prec);
    a.limb * b.limb

val mul_len: a:mpfr_reg_fp -> b:mpfr_reg_fp ->
    Tot (rl:pos{mul_limb a b >= pow2 (rl - 1) /\ mul_limb a b < pow2 rl})

let mul_len a b =
    if mul_limb a b < pow2 (a.len + b.len - 1) then begin
        lemma_mul_le_left a.limb (pow2 (b.len - 1)) b.limb;
	lemma_pow2_mul_range a.limb (b.len - 1) a.len;
        a.len + b.len - 1
    end else begin
        lemma_mul_lt_left a.limb b.limb (pow2 b.len);
	lemma_pow2_mul_range a.limb b.len a.len;
        a.len + b.len
    end

let mul_exp a b = 
    if mul_limb a b < pow2 (a.len + b.len - 1) then a.exp + b.exp - 1 else a.exp + b.exp

let mul_prec a b = mul_len a b + a.prec + b.prec - a.len - b.len

(* Multiplication for two MPFR numbers *)
val mul_exact: a:mpfr_reg_fp -> b:mpfr_reg_fp ->
    Tot (r:normal_fp{eval_abs a *. eval_abs b =. eval_abs r})

let mul_exact a b =
    mk_normal (a.sign * b.sign) (mul_prec a b) (mul_exp a b) (mul_limb a b) (mul_len a b) MPFR_NUM
