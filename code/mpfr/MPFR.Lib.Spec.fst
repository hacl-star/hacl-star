module MPFR.Lib.Spec

open FStar.Mul
open MPFR.Dyadic
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* MPFR uses 'mpfr_sign', 'mpfr_prec', 'mpfr_exp' and 'mpfr_d' to describe a dyadic rational number,
 * it also allows "sigular" values for NaN, +-Inf and +-ZERO.
 * for regular values, aka non-zero values,
 * 'mpfr_d' is an array of uint64 represents the significand in the following way:
 * it should start with bit '1' and the last certain bits (depends on precision) should be '0's
 * thus it represent a number in [0.5, 1) by adding '0.' in front of it.
 * Therefore, the whole mpfr_struct should represent a value:
 *             mpfr_sign * mpfr_d * 2^mpfr_exp.
 * In this file a struct is defined to store MPFR format floating point number. *)


///////////////////////////////////////////////////////
//  Struct Definition                                //
//  Used to store MPFR format floating point number  //
///////////////////////////////////////////////////////

(* indicating regular/sigular value type *)
type fp_type_t =
   | MPFR_NUM      (* regular number (excludes zero) *)
   | MPFR_ZERO     (* +0 or -0                       *)
   | MPFR_INF      (* +inf or -inf                   *)
   | MPFR_NAN      (* not a number                   *)
   
(* flag: indicates value type, other entries are useless for sigular value (except sign)
 * sign: sign of the value, indicates also the sign of zero and infinity
 * prec: precision of the value, see more information below with limb
 * exp : exponent of the value
 * len : the bit length of significand, see more information below with limb
 * limb: significand of the value, it is a 'len'-bit natural number (possibly with leading zeros),
         the first 'prec' bits can have values while the last 'len - prec' bits should be 0s.
	 it represents a rational number between 0 and 1 by adding '0.' in front of it *)
type fp_struct = {
    sign: s:int{s = -1 \/ s = 1};
    prec: pos;
    exp : int;
    limb: nat;
    len : pos;
    flag: fp_type_t
}

(* constructor *)
let mk_struct sign prec exp limb len flag = {
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
let eval (fp:valid_fp) = mk_fp (fp.sign * fp.limb) (fp.exp - fp.len)

val eval_abs: fp:valid_fp -> Tot (r:dyadic{r == fabs (eval fp)})
let eval_abs fp = mk_fp fp.limb (fp.exp - fp.len)

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
    (requires (valid_fp_cond (mk_struct sign prec exp limb len flag) /\
              normal_fp_cond (mk_struct sign prec exp limb len flag)))
    (ensures  (fun _ -> True)) =
    mk_struct sign prec exp limb len flag


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

(* validity for normal number of MPFR 
 * len should coordinate with prec and range limits for prec and exp *)
let mpfr_reg_fp_cond (s:normal_fp) =
    s.len = prec_to_len s.prec /\
    mpfr_PREC_COND s.prec /\
    mpfr_EXP_COND s.exp

(* type for normal number of MPFR *)
type mpfr_reg_fp = f:normal_fp{mpfr_reg_fp_cond f}

(* validity for MPFR number allowing sigular values
 * NaN, Inf, Zeros and normalized regular number *)
let mpfr_fp_cond (s:fp_struct) =
    MPFR_NAN? s.flag \/ MPFR_INF? s.flag \/ valid_zero_cond s \/ 
    (valid_fp_cond s /\ normal_fp_cond s /\ mpfr_reg_fp_cond s)

(* type for MPFR number *)
type mpfr_fp = s:fp_struct{mpfr_fp_cond s}


/////////////////////////////////////////////////////////////
//  Useful functions and lemmas for normal number of MPFR  //
/////////////////////////////////////////////////////////////

(* overflow bound for normal number of MPFR *)
val mpfr_overflow_bound: p:nat{mpfr_PREC_COND p} -> Tot dyadic

let mpfr_overflow_bound p =
    let l = prec_to_len p in
    mk_fp (pow2 l - pow2 (l - p)) (mpfr_EMAX_spec - l)

val mpfr_overflow_bound_lemma: p:nat{mpfr_PREC_COND p} -> f:mpfr_reg_fp{f.prec = p} -> Lemma
    (eval_abs f <=. mpfr_overflow_bound p)
    [SMTPat (eval_abs f <=. mpfr_overflow_bound p)]

let mpfr_overflow_bound_lemma p f =
    let l = prec_to_len p in
    lemma_pow2_le (l - p) l;
    lemma_pow2_mod l (l - p);
    lemma_mod_distr_sub_zero (pow2 l) (pow2 (l - p)) (pow2 (l - p));
    //! assert((pow2 l - pow2 (l - p)) % pow2 (l - p) = 0);
    lemma_pow2_le (l - p) (l - 1);
    lemma_pow2_double (l - 1);
    //! assert(pow2 l - pow2 (l - p) >= pow2 (l - 1));
    let b = mk_normal 1 p mpfr_EMAX_spec (pow2 l - pow2 (l - p)) l MPFR_NUM in
    //! assert(eval b == mpfr_overflow_bound p);
    let elb = min (f.exp - l) (mpfr_EMAX_spec - l) in
    lemma_pow2_multiple_le f.limb l (l - p);
    //! assert(f.limb <= pow2 l - pow2 (l - p));
    lemma_pow2_le (f.exp - l - elb) (mpfr_EMAX_spec - l - elb);
    assert(f.limb * pow2 (f.exp - l - elb) <= (pow2 l - pow2 (l - p)) * pow2 (mpfr_EMAX_spec - l - elb))
