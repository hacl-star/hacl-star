module MPFR.RoundingMode

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
