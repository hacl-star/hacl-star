module MPFR.Lib.Spec

open FStar.Mul
open MPFR.FloatingPoint
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"


///////////////////////////////////////////////////////
//  Struct Definition                                //
//  Used to store IEEE format floating point number  //
///////////////////////////////////////////////////////

(* Note that 0 is not supported *)
type fp_struct = {
    sign: (s:int{s = -1 \/ s = 1});
    prec: pos;
    exp : int;
    limb: nat;
    len : pos;
}

let mk_struct sign prec exp limb len = {
    sign = sign;
    prec = prec;
    exp  = exp;
    limb = limb;
    len  = len
}

(* Get bit length of a positive integer *)
val bits: m:pos -> Tot (p:pos{pow2 (p - 1) <= m /\ m < pow2 p})
let bits m = log2 m + 1

type valid_struct = s:fp_struct{s.limb = 0 \/ bits s.limb <= s.len}

(* Evaluation. Here is the method.
 * Firstly add '0.' in front of 'limb' to make it a floating number in (0, 1)
 * Then multiply it with 2 ^ exp *)
let eval (fp:fp_struct) = mk_fp (fp.sign * fp.limb) (fp.exp - fp.len)


/////////////////////////////////////////////////////////////////////////////////////////
//  Validity Test for ieee_struct                                                      //
//  A valid struct represents a binary floating point number defined in MPFR.BinaryFP  //
//  Important function 'eval' maps ieee_fp to floating_point                                //
/////////////////////////////////////////////////////////////////////////////////////////

(* Condition for validity 
 * A valid struct should have a positive precision which is smaller than 'limb' length
 * Only the first 'prec' bits of 'limb' store value and the rest bits are 0s *)
let ieee_valid_cond (s:fp_struct) =
    s.limb > 0 /\ bits s.limb = s.len /\
    0 < s.prec /\ s.prec <= s.len /\
    s.limb % pow2 (s.len - s.prec) = 0
    
type ieee_fp = s:valid_struct{ieee_valid_cond s}

let mk_ieee sign prec exp limb len: Pure ieee_fp
    (requires (ieee_valid_cond (mk_struct sign prec exp limb len)))
    (ensures  (fun _ -> True)) =
    mk_struct sign prec exp limb len


//////////////////////////////////////////////////////
//  A special type corresponding to top level code  //
//  Pure version of mpfr_struct                     //
//////////////////////////////////////////////////////

(* Condition for parameters range corresponding to top level code *)
let gmp_NUMB_BITS = 64
let mpfr_PREC_MIN = 1
let mpfr_PREC_MAX = pow2 31 - 1
let mpfr_PREC_COND (p:pos) = mpfr_PREC_MIN <= p /\ p <= mpfr_PREC_MAX

let mpfr_EXP_INVALID = pow2 30
let mpfr_EMIN = 1 - mpfr_EXP_INVALID
let mpfr_EMAX = mpfr_EXP_INVALID - 1
let mpfr_EXP_COND (x:int) = mpfr_EMIN <= x /\ x <= mpfr_EMAX

(* Condition for a MPFR floating number
 * The precision and exponent have range limits
 * The bit length of limb must be a multiple of 64 and as small as possible *)
val arr_size: p:pos ->
    Tot (s:pos{s % 64 = 0 /\ s >= p /\ s - 64 < p})
let arr_size p = ((p + 63) / 64) * 64

let mpfr_valid_cond (s:ieee_fp) =
    s.len = arr_size s.prec /\
    mpfr_PREC_COND s.prec /\
    mpfr_EXP_COND s.exp

type mpfr_fp = f:ieee_fp{mpfr_valid_cond f}
