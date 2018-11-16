module MPFR.RoundingMode

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* rounding modes *)
type mpfr_rnd_t = 
   | MPFR_RNDN 
   | MPFR_RNDZ
   | MPFR_RNDU
   | MPFR_RNDD
   | MPFR_RNDA

val mpfr_IS_LIKE_RNDZ: rnd:mpfr_rnd_t -> neg:bool -> Tot bool
let mpfr_IS_LIKE_RNDZ rnd neg =
    MPFR_RNDZ? rnd || (MPFR_RNDU? rnd && neg) || (MPFR_RNDD? rnd && not neg)

val mpfr_IS_LIKE_RNDA: rnd:mpfr_rnd_t -> neg:bool -> Tot bool
let mpfr_IS_LIKE_RNDA rnd neg =
    MPFR_RNDA? rnd || (MPFR_RNDD? rnd && neg) || (MPFR_RNDD? rnd && not neg)
