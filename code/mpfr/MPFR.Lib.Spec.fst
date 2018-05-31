module MPFR.Lib.Spec


let gmp_NUMB_BITS_spec = 64
let mpfr_PREC_MIN_spec = 1
let mpfr_PREC_MAX_spec = gmp_NUMB_BITS_spec - 1
let mpfr_EXP_INVALID_spec = pow2 30
let mpfr_EMIN_spec = 1 - mpfr_EXP_INVALID_spec
let mpfr_EMAX_spec = mpfr_EXP_INVALID_spec - 1
let mpfr_SIGN_POS  = 1
let mpfr_SIGN_NEG  = -1

let mpfr_prec_cond (p:pos) = mpfr_PREC_MIN_spec <= p /\ p <= mpfr_PREC_MAX_spec
let mpfr_exp_cond  (x:int) = mpfr_EMIN_spec <= x /\ x <= mpfr_EMAX_spec
let mpfr_sign_cond (s:int) = s = mpfr_SIGN_POS \/ s = mpfr_SIGN_NEG

type mpfr_structP = {
    sign: int;
    prec: pos;
    mant: nat;
    exp : int
}

let mpfr_mp_cond (s:mpfr_structP) = pow2 (s.prec - 1) <= s.mant /\ s.mant < pow2 s.prec

let valid_mpfr_struct (s:mpfr_structP) =
    mpfr_prec_cond s.prec /\ mpfr_exp_cond s.exp /\ mpfr_sign_cond s.sign /\
    mpfr_mp_cond s

