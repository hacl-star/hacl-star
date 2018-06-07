module MPFR.Lib.Spec

(* Pure version of mpfr_struct for internal calculations *)
(* This struct describe a number: sign * mant * 2^exp    *)
type mpfr_structP = {
    sign: s:int{s = 1 \/ s = -1};
    prec: pos;
    mant: nat;
    exp : int
}

(* Condition for validity *)
let mpfr_mp_cond (s:mpfr_structP) = pow2 (s.prec - 1) <= s.mant /\ s.mant < pow2 s.prec

(* Condition for parameters range corresponding to top level code *)
let mpfr_PREC_MIN_P = 1
let mpfr_PREC_MAX_P = 63
let mpfr_EMIN_P = 1 - pow2 30 - mpfr_PREC_MAX_P
let mpfr_EMAX_P = pow2 30 - 1 - mpfr_PREC_MIN_P
let mpfr_range_cond (s:mpfr_structP) =
    mpfr_PREC_MIN_P <= s.prec /\ s.prec <= mpfr_PREC_MAX_P /\
    mpfr_EMIN_P <= s.exp /\ s.exp <= mpfr_EMAX_P

let valid_structP (s:mpfr_structP) = mpfr_mp_cond s /\ mpfr_range_cond s
