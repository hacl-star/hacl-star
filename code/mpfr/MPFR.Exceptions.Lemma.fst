module MPFR.Exceptions.Lemma

open FStar.Mul
open FStar.UInt64

open MPFR.Maths
open MPFR.Dyadic
open MPFR.Lib.Spec
open MPFR.Round.Spec
open MPFR.RoundingMode

#set-options "--z3refresh --z3rlimit 40 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

let mpfr_overflow_spec (a:normal_fp{a.exp > mpfr_EMAX_spec}) 
    (p:pos{p <= a.prec /\ mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t) =
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign = -1) then mpfr_max_value a.sign p
    else mpfr_inf a.sign p

let mpfr_overflow_ternary_spec (a:normal_fp{a.exp > mpfr_EMAX_spec})
    (p:pos{p <= a.prec /\ mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t) =
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign = -1) then (-a.sign)
    else a.sign

val mpfr_overflow_post_cond_lemma: a:normal_fp{a.exp > mpfr_EMAX_spec} ->
    p:pos{p <= a.prec /\ mpfr_PREC_COND p} -> rnd_mode:mpfr_rnd_t ->
    f:int -> r:mpfr_fp{r.prec = p} -> Lemma
    (requires (r == mpfr_overflow_spec a p rnd_mode /\
               f = mpfr_overflow_ternary_spec a p rnd_mode))
    (ensures  (mpfr_round_cond a p rnd_mode r /\
               mpfr_ternary_cond f a r))

let mpfr_overflow_post_cond_lemma a p rnd_mode f r =
    exp_impl_overflow_lemma (round_def a p rnd_mode);
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign = -1) then begin
	exp_impl_overflow_lemma (high_mant a p);
        if a.sign = 1 then eval_lt_intro_lemma (mpfr_max_value a.sign p) (high_mant a p)
	else eval_lt_intro_lemma (high_mant a p) (mpfr_max_value a.sign p)
    end else ()
