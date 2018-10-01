module MPFR.Exceptions

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64

module ST = FStar.HyperStack.ST
module I32 = FStar.Int32
module U32 = FStar.UInt32

open MPFR.Maths
open MPFR.Dyadic
open MPFR.Lib
open MPFR.Lib.Spec
open MPFR.Round.Spec

open MPFR.Exceptions.Lemma

#set-options "--z3refresh --z3rlimit 30 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

val mpfr_overflow: x:mpfr_ptr -> rnd_mode:mpfr_rnd_t -> sign:mpfr_sign_t ->
    Stack i32
    (requires (fun h -> 
        let p = (as_struct h x).mpfr_prec in
        let l = (U32.v p - 1) / 64 + 1 in
        mpfr_live h x /\ mpfr_PREC_COND (U32.v p) /\
	length (as_struct h x).mpfr_d = l))
    (ensures  (fun h0 t h1 ->
        let p = (as_struct h1 x).mpfr_prec in
        mpfr_live h1 x /\ mpfr_modifies x h0 h1 /\
        mpfr_valid_cond h1 x /\ (as_struct h1 x).mpfr_sign = sign /\
	(forall (exact:normal_fp{exact.sign = I32.v sign /\ exact.exp > mpfr_EMAX_spec /\
	                    exact.prec >= U32.v p}).
	as_fp h1 x == mpfr_overflow_spec exact (U32.v p) rnd_mode /\
	I32.v t = mpfr_overflow_ternary_spec exact (U32.v p) rnd_mode)))

let mpfr_overflow x rnd_mode sign =
    mpfr_SET_SIGN x sign;
    if mpfr_IS_LIKE_RNDZ rnd_mode (mpfr_IS_NEG_SIGN sign) then begin
	mpfr_setmax x;
	mpfr_NEG_SIGN sign
    end else begin
        mpfr_SET_INF x;
	sign
    end

val mpfr_underflow: x:mpfr_ptr -> rnd_mode:mpfr_rnd_t -> sign:mpfr_sign_t ->
    Stack i32
    (requires (fun h -> 
        let p = (as_struct h x).mpfr_prec in
        let l = (U32.v p - 1) / 64 + 1 in
        mpfr_live h x /\ mpfr_PREC_COND (U32.v p) /\
	length (as_struct h x).mpfr_d = l))
    (ensures  (fun h0 t h1 ->
        let p = (as_struct h1 x).mpfr_prec in
        mpfr_live h1 x /\ mpfr_modifies x h0 h1 /\
        mpfr_valid_cond h1 x /\ (as_struct h1 x).mpfr_sign = sign /\
	(forall (exact:normal_fp{exact.sign = I32.v sign /\ exact.exp < mpfr_EMIN_spec /\
	                    exact.prec >= U32.v p}).
	as_fp h1 x == mpfr_underflow_spec exact (U32.v p) rnd_mode /\
	I32.v t = mpfr_underflow_ternary_spec exact (U32.v p) rnd_mode)))

let mpfr_underflow x rnd_mode sign =
    mpfr_SET_SIGN x sign;
    if mpfr_IS_LIKE_RNDZ rnd_mode (mpfr_IS_NEG_SIGN sign) then begin
        mpfr_SET_ZERO x;
	mpfr_NEG_SIGN sign
    end else begin
        mpfr_setmin x;
	sign
    end
