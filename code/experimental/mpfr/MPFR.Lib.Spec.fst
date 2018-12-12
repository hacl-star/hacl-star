module MPFR.Lib.Spec

open FStar.Mul
open MPFR.Dyadic
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 30 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* MPFR uses 'mpfr_sign', 'mpfr_prec', 'mpfr_exp' and 'mpfr_d' to describe a dyadic rational number,
 * it also allows "sigular" values for NaN, +-Inf and +-Zero.
 * for regular values, aka non-zero values,
 * 'mpfr_d' is an array of uint64 represents the significand in the following way:
 * it should start with bit '1' and the last certain bits (depends on precision) should be '0's
 * thus it represent a number in [0.5, 1) by adding '0.' in front of it.
 * Therefore, the whole mpfr_struct should represent a value:
 *             mpfr_sign * mpfr_d * 2 ^ mpfr_exp.
 * In this file a struct is defined to store MPFR format floating point number. *)


///////////////////////////////////////////////////////
//  Struct Definition                                //
//  Used to store MPFR format floating point number  //
///////////////////////////////////////////////////////

(* indicating regular/sigular value type *)
type fp_type_t =
   | MPFR_NUM      (* regular number (non-zero) *)
   | MPFR_ZERO     (* +0 or -0                  *)
   | MPFR_INF      (* +inf or -inf              *)
   | MPFR_NAN      (* not a number              *)

type fp_sign_t = s:int{s = -1 \/ s = 1}
   
(* flag: indicates value type, other entries are useless for sigular value (except sign)
 * sign: sign of the value, indicates also the sign of zero and infinity
 * prec: precision of the value, see more information below with limb
 * exp : exponent of the value
 * len : the bit length of significand, see more information below with limb
 * limb: significand of the value,
 *       it is a 'len'-bit natural number (possibly with leading zeros),
 *       the first 'prec' bits can have values while the last 'len - prec' bits should be 0s.
 *	 it represents a rational number between 0 and 1 by adding '0.' in front of it *)
type fp_struct = {
    sign: fp_sign_t;
    prec: pos;
    exp : int;
    limb: nat;
    len : pos;
    flag: fp_type_t
}

(* constructor *)
let mk_fp_struct sign prec exp limb len flag = {
    sign = sign;
    prec = prec;
    exp  = exp;
    limb = limb;
    len  = len;
    flag = flag
}


///////////////////////////////////////////////////////////////////////////////////////////
//  Evaluation for the struct                                                            //
//  Only regular numbers and +-0 can be evaluated to a dyadic                            //
//  The precision should be positive and not greater than the bit length of significand  //
//  Also the last 'len - prec' bits should be 0s                                         //
///////////////////////////////////////////////////////////////////////////////////////////

(* validity for NaN and Inf *)
let valid_nan_cond s = MPFR_NAN? s.flag
let valid_inf_cond s = MPFR_INF? s.flag

(* validity for zero
 * flag = MPFR_ZERO and limb = 0 *)
let valid_zero_cond s = MPFR_ZERO? s.flag /\ s.limb = 0

(* validity for non-zero 
 * flag = MPFR_NUM, limb is a 'len'-bit positive integer and last 'len - prec' bits are 0s *)
let valid_num_cond s =
    MPFR_NUM? s.flag /\ 0 < s.limb /\ s.limb < pow2 s.len /\
    0 < s.prec /\ s.prec <= s.len /\
    s.limb % pow2 (s.len - s.prec) = 0

(* validity for evaluation
 * only zeros and regular numbers can be evaluated *)
let valid_fp_cond s = valid_zero_cond s \/ valid_num_cond s

(* type for fp_struct which can be evaluated *)
type valid_fp = s:fp_struct{valid_fp_cond s}

(* Evaluation.
 * Firstly add '0.' in front of 'limb' to make it a floating number in (0, 1)
 * Then multiply it with 2 ^ exp *)
let eval (fp:valid_fp) = mk_dyadic (fp.sign * fp.limb) (fp.exp - fp.len)

val eval_abs: fp:valid_fp -> Tot (r:dyadic{r == fabs (eval fp) /\ r >=. zero_dyadic /\ r >=. eval fp})
let eval_abs fp = mk_dyadic fp.limb (fp.exp - fp.len)


//////////////////////////////////////////////////////////////////////
//  Normalize a regular value                                       //
//  A regular value is called normal when there's no leading zeros  //
//////////////////////////////////////////////////////////////////////

(* validity for normal number
 * should be a regular number, and normalized *)
let normal_fp_cond (s:valid_fp) = valid_num_cond s /\ s.limb >= pow2 (s.len - 1)

(* type for normal number *)
type normal_fp = s:valid_fp{normal_fp_cond s}

(* constructor for normal number *)
let mk_normal sign prec exp limb len flag: Pure normal_fp
    (requires (valid_fp_cond (mk_fp_struct sign prec exp limb len flag) /\
              normal_fp_cond (mk_fp_struct sign prec exp limb len flag)))
    (ensures  (fun _ -> True)) =
    mk_fp_struct sign prec exp limb len flag

(* lemmas which intro comparison between two evaluated values *)
val eval_eq_intro_lemma: a:valid_fp -> b:valid_fp -> Lemma
    (requires (eval_abs a =. eval_abs b /\ a.sign = b.sign))
    (ensures  (eval a =. eval b))
    [SMTPat (eval_abs a =. eval_abs b); SMTPat (a.sign = b.sign)]
let eval_eq_intro_lemma a b = ()

val eval_abs_lt_intro_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (let elb = min (a.exp - a.len) (b.exp - b.len) in
               a.exp < b.exp \/ (a.exp = b.exp /\
	       a.limb * pow2 (a.exp - a.len - elb) < b.limb * pow2 (b.exp - b.len - elb))))
    (ensures  (eval_abs a <. eval_abs b))

let eval_abs_lt_intro_lemma a b =
    if a.exp = b.exp then () else begin
        let elb = min (a.exp - a.len) (b.exp - b.len) in
	lemma_pow2_mul_range a.limb (a.exp - a.len - elb) a.len;
	lemma_pow2_mul_range b.limb (b.exp - b.len - elb) b.len;
        lemma_pow2_le (a.exp - elb) (b.exp - 1 - elb)
    end

val eval_abs_le_intro_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (let elb = min (a.exp - a.len) (b.exp - b.len) in
               a.exp < b.exp \/ (a.exp = b.exp /\
	       a.limb * pow2 (a.exp - a.len - elb) <= b.limb * pow2 (b.exp - b.len - elb))))
    (ensures  (eval_abs a <=. eval_abs b))

let eval_abs_le_intro_lemma a b =
    if a.exp = b.exp then () else eval_abs_lt_intro_lemma a b

val eval_lt_intro_lemma: a:valid_fp -> b:valid_fp -> Lemma
    (requires ((a.sign < b.sign /\ ~(eval_abs a =. zero_dyadic /\ eval_abs b =. zero_dyadic)) \/
              (a.sign = b.sign /\ a.sign > 0 /\ eval_abs a <. eval_abs b) \/
	      (a.sign = b.sign /\ a.sign < 0 /\ eval_abs a >. eval_abs b)))
    (ensures  (eval a <. eval b))
let eval_lt_intro_lemma a b = ()

val eval_le_intro_lemma: a:valid_fp -> b:valid_fp -> Lemma
    (requires (a.sign < b.sign \/
              (a.sign > b.sign /\ eval_abs a =. zero_dyadic /\ eval_abs b =. zero_dyadic) \/
              (a.sign = b.sign /\ a.sign > 0 /\ eval_abs a <=. eval_abs b) \/
	      (a.sign = b.sign /\ a.sign < 0 /\ eval_abs a >=. eval_abs b)))
    (ensures  (eval a <=. eval b))
let eval_le_intro_lemma a b = ()

(* lemmas which reveal the internal proprieties from comparisons *)
val eval_eq_reveal_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (eval a =. eval b))
    (ensures  (eval_abs a =. eval_abs b /\ a.sign = b.sign /\ a.exp = b.exp /\
              (forall (i:nat{i < min a.prec b.prec}). UInt.nth #a.len a.limb i = UInt.nth #b.len b.limb i)))
let eval_eq_reveal_lemma a b =
    let elb = min (a.exp - a.len) (b.exp - b.len) in
    lemma_pow2_mul_range a.limb (a.exp - a.len - elb) a.len;
    lemma_pow2_mul_range b.limb (b.exp - b.len - elb) b.len;
    lemma_bit_length (a.limb * pow2 (a.exp - a.len - elb)) (a.exp - elb) (b.exp - elb);
    //! assert(a.exp = b.exp);
    let mp = min a.prec b.prec in
    lemma_pow2_mul_div a.limb (a.exp - a.len - elb) (a.exp - mp - elb);
    lemma_pow2_mul_div b.limb (b.exp - b.len - elb) (b.exp - mp - elb);
    assert(a.limb / pow2 (a.len - mp) = b.limb / pow2 (b.len - mp));
    lemma_pow2_div_lt a.limb a.len (a.len - mp);
    lemma_pow2_div_lt b.limb b.len (b.len - mp);
    slice_left_nth_lemma #a.len a.limb mp;
    slice_left_nth_lemma #b.len b.limb mp

val eval_abs_lt_reveal_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (eval_abs a <. eval_abs b))
    (ensures  (let elb = min (a.exp - a.len) (b.exp - b.len) in
               a.exp <= b.exp /\
	       a.limb * pow2 (a.exp - a.len - elb) < b.limb * pow2 (b.exp - b.len - elb)))

let eval_abs_lt_reveal_lemma a b =
    let elb = min (a.exp - a.len) (b.exp - b.len) in
    lemma_pow2_mul_range a.limb (a.exp - a.len - elb) a.len;
    lemma_pow2_mul_range b.limb (b.exp - b.len - elb) b.len;
    if a.exp > b.exp then lemma_pow2_le (b.exp - elb) (a.exp - 1 - elb)

val eval_abs_le_reveal_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (eval_abs a <=. eval_abs b))
    (ensures  (let elb = min (a.exp - a.len) (b.exp - b.len) in
               a.exp <= b.exp /\
	       a.limb * pow2 (a.exp - a.len - elb) <= b.limb * pow2 (b.exp - b.len - elb)))

let eval_abs_le_reveal_lemma a b =
    let elb = min (a.exp - a.len) (b.exp - b.len) in
    lemma_pow2_mul_range a.limb (a.exp - a.len - elb) a.len;
    lemma_pow2_mul_range b.limb (b.exp - b.len - elb) b.len;
    if a.exp > b.exp then lemma_pow2_le (b.exp - elb) (a.exp - 1 - elb)

val eval_lt_reveal_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (eval a <. eval b))
    (ensures  (let elb = min (a.exp - a.len) (b.exp - b.len) in
               (a.sign < b.sign \/
               (a.sign = b.sign /\ a.sign > 0 /\ eval_abs a <. eval_abs b /\
	        (a.exp <= b.exp /\
		 a.limb * pow2 (a.exp - a.len - elb) < b.limb * pow2 (b.exp - b.len - elb))) \/
               (a.sign = b.sign /\ a.sign < 0 /\ eval_abs a >. eval_abs b /\
	        (a.exp >= b.exp /\
		 a.limb * pow2 (a.exp - a.len - elb) > b.limb * pow2 (b.exp - b.len - elb))))))

let eval_lt_reveal_lemma a b =
    if a.sign < b.sign || a.sign > b.sign then ()
    else if a.sign > 0 then eval_abs_lt_reveal_lemma a b
    else eval_abs_lt_reveal_lemma b a

val eval_le_reveal_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (eval a <=. eval b))
    (ensures  (let elb = min (a.exp - a.len) (b.exp - b.len) in
               (a.sign < b.sign \/
               (a.sign = b.sign /\ a.sign > 0 /\ eval_abs a <=. eval_abs b /\
	        (a.exp <= b.exp /\
		 a.limb * pow2 (a.exp - a.len - elb) <= b.limb * pow2 (b.exp - b.len - elb))) \/
               (a.sign = b.sign /\ a.sign < 0 /\ eval_abs a >=. eval_abs b /\
	        (a.exp >= b.exp /\
		 a.limb * pow2 (a.exp - a.len - elb) >= b.limb * pow2 (b.exp - b.len - elb))))))

let eval_le_reveal_lemma a b =
    if a.sign < b.sign || a.sign > b.sign then ()
    else if a.sign > 0 then eval_abs_le_reveal_lemma a b
    else eval_abs_le_reveal_lemma b a

(* change the length of the limb (no less than prec) keeps the value unchanged *)
val change_len: a:normal_fp -> l:nat{l >= a.prec} ->
    Tot (r:normal_fp{r.len = l /\ eval r =. eval a})

let change_len a l =
    if l >= a.len then begin
        lemma_pow2_mul_range a.limb (l - a.len) a.len;
	lemma_pow2_mul_mod a.limb (l - a.len) (l - a.prec);
        {a with limb = a.limb * pow2 (l - a.len); len = l}
    end else begin
        lemma_pow2_div_range a.limb (a.len - l) a.len;
	lemma_pow2_mod_div a.limb (a.len - a.prec) (a.len - l);
	lemma_pow2_mod_mod_zero a.limb (a.len - a.prec) (a.len - l);
	lemma_pow2_div_mul a.limb (a.len - l) (a.len - l);
        {a with limb = a.limb / pow2 (a.len - l); len = l}
    end

////////////////////////////////////////////////////////////////////////////////
//  Pure version of mpfr_struct                                               //
//  A MPFR number has limits for its precision and exponent                   //
//  The bit length of limb must be a multiple of 64 and as small as possible  //
////////////////////////////////////////////////////////////////////////////////

(* range limits for precision and exponent *)
let mpfr_PREC_MIN_spec = 1
let mpfr_PREC_MAX_spec = pow2 31 - 1

let mpfr_PREC_COND (p:nat) = mpfr_PREC_MIN_spec <= p /\ p <= mpfr_PREC_MAX_spec

let mpfr_EMIN_spec = 1 - pow2 30
let mpfr_EMAX_spec = pow2 30 - 1

let mpfr_EXP_COND  (x:int) = mpfr_EMIN_spec <= x /\ x <= mpfr_EMAX_spec

(* get len from prec for a MPFR number *)
val prec_to_len: p:pos ->
    Tot (s:pos{s % 64 = 0 /\ s >= p /\ s - 64 < p})
let prec_to_len p = ((p + 63) / 64) * 64

let mpfr_len_cond (p:pos) (l:nat) = l = prec_to_len p

(* validity for normal number of MPFR 
 * len should coordinate with prec and range limits for prec and exp *)
let mpfr_reg_fp_cond (s:normal_fp) =
    mpfr_len_cond s.prec s.len /\
    mpfr_PREC_COND s.prec /\
    mpfr_EXP_COND s.exp

(* type for normal number of MPFR *)
type mpfr_reg_fp = f:normal_fp{mpfr_reg_fp_cond f}

(* validity for MPFR number allowing sigular values
 * NaN, Inf, Zeros and normalized regular number *)
let mpfr_fp_cond (s:fp_struct) =
    mpfr_len_cond s.prec s.len /\
    (MPFR_NAN? s.flag \/ MPFR_INF? s.flag \/ valid_zero_cond s \/ 
    (valid_fp_cond s /\ normal_fp_cond s /\ mpfr_reg_fp_cond s))

(* type for MPFR number *)
type mpfr_fp = s:fp_struct{mpfr_fp_cond s}

(* singular values constructor *)
let mpfr_nan (p:nat{mpfr_PREC_COND p}):
    Tot (x:mpfr_fp{valid_nan_cond x /\ x.prec = p}) =
    mk_fp_struct 1 p 0 0 (prec_to_len p) MPFR_NAN

let mpfr_inf (s:fp_sign_t) (p:nat{mpfr_PREC_COND p}):
    Tot (x:mpfr_fp{valid_inf_cond x /\ x.sign = s /\ x.prec = p}) =
    mk_fp_struct s p 0 0 (prec_to_len p) MPFR_INF

let mpfr_zero (s:fp_sign_t) (p:nat{mpfr_PREC_COND p}):
    Tot (x:mpfr_fp{valid_zero_cond x /\ x.sign = s /\ x.prec = p /\
                   eval_abs x =. zero_dyadic /\ eval x =. zero_dyadic}) =
    mk_fp_struct s p 0 0 (prec_to_len p) MPFR_ZERO

////////////////////////////////////////////////////
//  Overflow and underflow bound for MPFR number  //
//  Conversion from normal number to MPFR number  //
////////////////////////////////////////////////////

(* overflow bound for normal number of MPFR *)
val mpfr_overflow_bound: p:nat{mpfr_PREC_COND p} -> Tot (b:dyadic{b >. zero_dyadic})

let mpfr_overflow_bound p =
    let l = prec_to_len p in
    lemma_pow2_lt (l - p) l;
    mk_dyadic (pow2 l - pow2 (l - p)) (mpfr_EMAX_spec - l)

val mpfr_max_value: s:fp_sign_t -> p:nat{mpfr_PREC_COND p} ->
    Tot (m:mpfr_fp{valid_num_cond m /\ m.sign = s /\ m.prec = p /\ m.exp = mpfr_EMAX_spec /\
                   m.limb = pow2 (prec_to_len p) - pow2 (prec_to_len p - p) /\
                   eval_abs m =. mpfr_overflow_bound p})

let mpfr_max_value s p = 
    let l = prec_to_len p in
    lemma_pow2_lt (l - p) l;
    lemma_pow2_le (l - p) l;
    lemma_pow2_mod l (l - p);
    lemma_mod_distr_sub_zero (pow2 l) (pow2 (l - p)) (pow2 (l - p));
    //! assert((pow2 l - pow2 (l - p)) % pow2 (l - p) = 0);
    lemma_pow2_le (l - p) (l - 1);
    lemma_pow2_double (l - 1);
    //! assert(pow2 l - pow2 (l - p) >= pow2 (l - 1));
    mk_normal s p mpfr_EMAX_spec (pow2 l - pow2 (l - p)) l MPFR_NUM

(* underflow bound for normal number of MPFR *)
val mpfr_underflow_bound: p:nat{mpfr_PREC_COND p} -> Tot (b:dyadic{b >. zero_dyadic})

let mpfr_underflow_bound p =
    let l = prec_to_len p in
    mk_dyadic (pow2 (l - 1)) (mpfr_EMIN_spec - l)

val mpfr_min_value: s:fp_sign_t -> p:nat{mpfr_PREC_COND p} ->
    Tot (m:mpfr_fp{valid_num_cond m /\ m.sign = s /\ m.prec = p /\ m.exp = mpfr_EMIN_spec /\
                   m.limb = pow2 (prec_to_len p - 1) /\
                   eval_abs m =. mpfr_underflow_bound p})

let mpfr_min_value s p = 
    let l = prec_to_len p in
    lemma_pow2_mod (l - 1) (l - p);
    //! assert(pow2 (l - 1) % pow2 (l - p) = 0);
    mk_normal s p mpfr_EMIN_spec (pow2 (l - 1)) l MPFR_NUM

(* lemmas about overflow/underflow *)
val exp_impl_no_overflow_lemma: s:normal_fp{mpfr_PREC_COND s.prec /\ s.exp <= mpfr_EMAX_spec} -> Lemma
    (eval_abs s <=. mpfr_overflow_bound s.prec /\
     not (eval_abs s >. mpfr_overflow_bound s.prec))

let exp_impl_no_overflow_lemma s =
    let p, l = s.prec, prec_to_len s.prec in
    let s' = change_len s l in
    lemma_pow2_multiple_le s'.limb l (l - p);
    eval_abs_le_intro_lemma s (mpfr_max_value s.sign s.prec)

val no_overflow_impl_exp_lemma: s:normal_fp{mpfr_PREC_COND s.prec} -> Lemma
    (requires (eval_abs s <=. mpfr_overflow_bound s.prec))
    (ensures  (s.exp <= mpfr_EMAX_spec))

let no_overflow_impl_exp_lemma s =
    let s' = change_len s (prec_to_len s.prec) in
    eval_eq_reveal_lemma s s';
    eval_abs_le_reveal_lemma s' (mpfr_max_value s'.sign s'.prec)

val exp_impl_overflow_lemma: s:normal_fp{mpfr_PREC_COND s.prec /\ s.exp > mpfr_EMAX_spec} -> Lemma
    (eval_abs s >. mpfr_overflow_bound s.prec /\
     not (eval_abs s <=. mpfr_overflow_bound s.prec))

let exp_impl_overflow_lemma s =
    if (eval_abs s <=. mpfr_overflow_bound s.prec) then no_overflow_impl_exp_lemma s

val overflow_impl_exp_lemma: s:normal_fp{mpfr_PREC_COND s.prec} -> Lemma
    (requires (eval_abs s >. mpfr_overflow_bound s.prec))
    (ensures  (s.exp > mpfr_EMAX_spec))

let overflow_impl_exp_lemma s =
    if s.exp <= mpfr_EMAX_spec then exp_impl_no_overflow_lemma s

val exp_impl_no_underflow_lemma: s:normal_fp{mpfr_PREC_COND s.prec /\ s.exp >= mpfr_EMIN_spec} -> Lemma
    (eval_abs s >=. mpfr_underflow_bound s.prec /\
     not (eval_abs s <. mpfr_underflow_bound s.prec))

let exp_impl_no_underflow_lemma s =
    let p, l = s.prec, prec_to_len s.prec in
    lemma_pow2_mod (l - 1) (l - p);
    //! assert(pow2 (l - 1) % pow2 (l - p) = 0);
    let s' = change_len s l in
    eval_abs_le_intro_lemma (mpfr_min_value s.sign s.prec) s

val no_underflow_impl_exp_lemma: s:normal_fp{mpfr_PREC_COND s.prec} -> Lemma
    (requires (eval_abs s >=. mpfr_underflow_bound s.prec))
    (ensures  (s.exp >= mpfr_EMIN_spec))

let no_underflow_impl_exp_lemma s =
    let s' = change_len s (prec_to_len s.prec) in
    eval_eq_reveal_lemma s s';
    eval_abs_le_reveal_lemma (mpfr_min_value s'.sign s'.prec) s'

val exp_impl_underflow_lemma: s:normal_fp{mpfr_PREC_COND s.prec /\ s.exp < mpfr_EMIN_spec} -> Lemma
    (eval_abs s <. mpfr_underflow_bound s.prec /\
     not (eval_abs s >=. mpfr_underflow_bound s.prec))

let exp_impl_underflow_lemma s =
    if eval_abs s >=. mpfr_underflow_bound s.prec then no_underflow_impl_exp_lemma s

val underflow_impl_exp_lemma: s:normal_fp{mpfr_PREC_COND s.prec} -> Lemma
    (requires (eval_abs s <. mpfr_underflow_bound s.prec))
    (ensures  (s.exp < mpfr_EMIN_spec))

let underflow_impl_exp_lemma s =
    if s.exp >= mpfr_EMIN_spec then exp_impl_no_underflow_lemma s
