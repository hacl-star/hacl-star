module MPFR.Add1.Spec

open FStar.Mul
open MPFR.Dyadic
open MPFR.Lib.Spec
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 15 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* In this specification we only consider MPFR normal numbers as input *)

(* Useful functions when adding two MPFR numbers with same precision
 * and the exponent of the first one is greater than that of the second one *)
val add1sp_ge_limb: a:mpfr_reg_fp ->
    b:mpfr_reg_fp{a.prec = b.prec /\ a.exp >= b.exp} ->
    Tot (rm:nat{rm = (eval_abs a +. eval_abs b).significand /\ rm % pow2 (a.len - a.prec) = 0})

let add1sp_ge_limb a b =
    assert((a.limb * pow2 (a.exp - b.exp) + b.limb) = (eval_abs a +. eval_abs b).significand);
    lemma_mul_mod_zero a.limb (pow2 (a.exp - b.exp)) (pow2 (a.len - a.prec));
    lemma_mod_distr_zero (a.limb * pow2 (a.exp - b.exp)) b.limb (pow2 (a.len - a.prec));
    //! assert((a.limb * pow2 (a.exp - b.exp) + b.limb) % pow2 (a.len - a.prec) = 0);
    a.limb * pow2 (a.exp - b.exp) + b.limb

val add1sp_ge_len: a:mpfr_reg_fp -> 
    b:mpfr_reg_fp{a.prec = b.prec /\ a.exp >= b.exp} ->
    Tot (rl:pos{add1sp_ge_limb a b >= pow2 (rl - 1) /\ add1sp_ge_limb a b < pow2 rl})

let add1sp_ge_len a b =
    let d = a.exp - b.exp in
    if add1sp_ge_limb a b < pow2 (a.len + d) then begin
	lemma_mul_le_right (pow2 d) (pow2 (a.len - 1)) a.limb;
	lemma_pow2_mul (a.len - 1) d;
	//! assert(pow2 (a.len - 1 + d) <= add_sp_ge_limb a b);
	a.len + d
    end else begin
        lemma_mul_lt_right (pow2 d) a.limb (pow2 a.len);
        lemma_pow2_mul a.len d;
	lemma_pow2_le b.len (a.len + d);
        lemma_pow2_double (a.len + d);
	//! assert(add_sp_ge_limb a b < pow2 (a.len + d + 1));
	a.len + d + 1
    end

let add1sp_ge_exp a b =
    if add1sp_ge_limb a b < pow2 (a.len + a.exp - b.exp) then a.exp else a.exp + 1

let add1sp_ge_prec a b = a.prec + add1sp_ge_len a b - a.len

(* Addition for two MPFR numbers with same precision *)
val add1sp_exact: a:mpfr_reg_fp ->
    b:mpfr_reg_fp{a.prec = b.prec} ->
    Tot (r:normal_fp{r.sign = a.sign /\ eval_abs a +. eval_abs b =. eval_abs r})
    
let add1sp_exact a b = 
    let rs = a.sign in
    let a, b = if a.exp >= b.exp then a, b else b, a in
    mk_normal rs (add1sp_ge_prec a b) (add1sp_ge_exp a b) (add1sp_ge_limb a b) (add1sp_ge_len a b) MPFR_NUM
