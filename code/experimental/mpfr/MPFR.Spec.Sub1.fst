module MPFR.Spec.Sub1

open FStar.Mul
open MPFR.Dyadic
open MPFR.Spec.Lib
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 15 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* In this specification we only consider MPFR normal numbers as input *)

(* Useful functions when subtracting two MPFR numbers with same precision
 * and the first one is greater than that the second one *)
val sub1sp_gt_limb: a:mpfr_reg_fp ->
    b:mpfr_reg_fp{a.prec = b.prec /\ a.exp >= b.exp /\ (gt (eval_abs a) (eval_abs b))} ->
    Tot (rm:pos{rm =(eval_abs a -. eval_abs b).significand})

let sub1sp_gt_limb a b =
    //! assert((a.limb * pow2 (a.exp - b.exp) - b.limb) = (eval_abs a -. eval_abs b).significand);
    lemma_mul_mod_zero a.limb (pow2 (a.exp - b.exp)) (pow2 (a.len - a.prec));
    a.limb * pow2 (a.exp - b.exp) - b.limb

val sub1sp_gt_len: a:mpfr_reg_fp -> 
    b:mpfr_reg_fp{a.prec = b.prec /\ a.exp >= b.exp /\ (gt (eval_abs a) (eval_abs b))} ->
    Tot (rl:pos{sub1sp_gt_limb a b >= pow2 (rl - 1) /\ sub1sp_gt_limb a b < pow2 rl})

let sub1sp_gt_len a b =
    lemma_pow2_nbits (sub1sp_gt_limb a b);
    nbits  (sub1sp_gt_limb a b)

let sub1sp_gt_exp a b =
    b.exp + sub1sp_gt_len a b - b.len
    
let sub1sp_gt_prec a b = // sub1sp_gt_len a b
    b.prec + sub1sp_gt_len a b - b.len
    
val lemma_fp_exp_ge: a:mpfr_reg_fp ->
    b:mpfr_reg_fp -> Lemma
    (requires (a.prec=b.prec /\ ge (eval_abs a) (eval_abs b)))
    (ensures (a.exp>=b.exp))
let lemma_fp_exp_ge a b=let elb=min (a.exp-a.len) (b.exp-b.len) in
       assert(a.limb * pow2 (a.exp-a.len-elb)>=b.limb * pow2 (b.exp-b.len-elb));
       assert(pow2 a.len * pow2 (a.exp-a.len-elb)>b.limb * pow2 (b.exp-b.len-elb));
       assert(pow2 a.len * pow2 (a.exp-a.len-elb)>pow2 (b.len-1) * pow2 (b.exp-b.len-elb));
       lemma_pow2_mul a.len (a.exp-a.len-elb);
       assert(pow2 (a.exp-elb)>pow2 (b.len-1) * pow2 (b.exp-b.len-elb));
       lemma_pow2_mul (b.len-1) (b.exp-b.len-elb);
       assert(pow2 (a.exp-elb)>pow2 (b.exp-1-elb));
       lemma_pow2_gt_rev (a.exp-elb) (b.exp-1-elb)

(* Subtraction for two MPFR numbers with same precision *)
val sub1sp_exact: a:mpfr_reg_fp ->
    b:mpfr_reg_fp{a.prec = b.prec} ->
    Tot (r:valid_fp{((gt (eval_abs a) (eval_abs b) /\ r.sign = a.sign) \/
                    (eq (eval_abs a) (eval_abs b)) \/
                    (lt (eval_abs a) (eval_abs b) /\ r.sign = -a.sign))
                    /\  fabs (eval_abs a -. eval_abs b) =. eval_abs r /\
                    (normal_fp_cond r \/ r.flag=MPFR_ZERO)})

let sub1sp_exact ar br = 
    if eq (eval_abs ar) (eval_abs br) then mpfr_zero 1 1 else
    let rs,a,b = if gt (eval_abs ar) (eval_abs br) then ar.sign,ar,br else -ar.sign,br,ar in
       lemma_fp_exp_ge a b;
       assume(sub1sp_gt_prec a b>0);
       let r=mk_fp_struct rs (sub1sp_gt_prec a b) (sub1sp_gt_exp a b) (sub1sp_gt_limb a b) (sub1sp_gt_len a b) MPFR_NUM in
       lemma_mul_mod_zero a.limb (pow2 (a.exp-b.exp)) (pow2 (r.len-r.prec));
       lemma_mod_distr_sub_zero (a.limb * pow2 (a.exp - b.exp)) b.limb (pow2 (r.len-r.prec));
       r
