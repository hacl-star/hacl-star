module MPFR.Add.Spec

open FStar.Mul
open MPFR.FloatingPoint
open MPFR.Lib.Spec
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Useful functions when adding two MPFR numbers with same precision
 * and the exponent of the first one is greater than that of the second one *)
val add_sp_ge_limb: a:mpfr_fp -> b:mpfr_fp -> Pure nat
    (requires (a.sign = b.sign /\ a.prec = b.prec /\ a.exp >= b.exp))
    (ensures  (fun rm -> rm = abs (eval a +. eval b).significand /\
                      rm % pow2 (a.len - a.prec) = 0))
    
let add_sp_ge_limb a b =
    lemma_mul_mod a.limb (pow2 (a.exp - b.exp)) (pow2 (a.len - a.prec));
    lemma_mod_distr (a.limb * pow2 (a.exp - b.exp)) b.limb (pow2 (a.len - a.prec));
    a.limb * pow2 (a.exp - b.exp) + b.limb
    
val add_sp_ge_exp: a:mpfr_fp -> b:mpfr_fp -> Pure int
    (requires (a.sign = b.sign /\ a.prec = b.prec /\ a.exp >= b.exp))
    (ensures  (fun rx -> rx - bits (add_sp_ge_limb a b) = (eval a +. eval b).exponent))

let add_sp_ge_exp a b =
    let d = a.exp - b.exp in
    if add_sp_ge_limb a b < pow2 (bits a.limb + d) then begin 
	lemma_mul_le_right (pow2 d) (pow2 (bits a.limb - 1)) a.limb;
	lemma_pow2_mul (bits a.limb - 1) d;
	lemma_log2_le (pow2 (bits a.limb - 1 + d)) (add_sp_ge_limb a b);
	lemma_log2_lt (add_sp_ge_limb a b) (bits a.limb + d);
        a.exp
    end else begin
	lemma_log2_le (pow2 (bits a.limb + d)) (add_sp_ge_limb a b);
        lemma_mul_lt_right (pow2 d) a.limb (pow2 (bits a.limb));
        lemma_pow2_mul (bits a.limb) d;
	lemma_pow2_le (bits b.limb) (bits a.limb + d);
        lemma_pow2_double (bits a.limb + d);
	lemma_log2_lt (add_sp_ge_limb a b) (bits a.limb + d + 1);
        a.exp + 1
    end
    
val add_sp_ge_prec: a:mpfr_fp -> b:mpfr_fp -> Pure pos
    (requires (a.sign = b.sign /\ a.prec = b.prec /\ a.exp >= b.exp))
    (ensures  (fun rp -> bits (add_sp_ge_limb a b) - rp = bits a.limb - a.prec))
    
let add_sp_ge_prec a b = a.prec + add_sp_ge_exp a b - b.exp

(* Addition for two MPFR numbers with same precision *)
val add_sp: a:mpfr_fp -> b:mpfr_fp -> Pure ieee_fp
    (requires (a.sign = b.sign /\ a.prec = b.prec))
    (ensures  (fun r -> eval a +. eval b =. eval r))
    
let add_sp a b = 
    let a, b = if a.exp >= b.exp then a, b else b, a in
    mk_ieee a.sign (add_sp_ge_prec a b) (add_sp_ge_exp a b) (add_sp_ge_limb a b) (bits (add_sp_ge_limb a b))
