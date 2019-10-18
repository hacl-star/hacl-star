module Vale.Math.Poly2.Galois.IntTypes
module U = FStar.UInt
open FStar.Mul
open Lib.IntTypes

val define_logand (t:inttype{unsigned t}) (a b:uint_t t SEC) : Lemma
  (requires t =!= U1)
  (ensures v (logand a b) == U.logand #(bits t) (v a) (v b))

val define_logor (t:inttype{unsigned t}) (a b:uint_t t SEC) : Lemma
  (requires t =!= U1)
  (ensures v (logor a b) == U.logor #(bits t) (v a) (v b))

val define_logxor (t:inttype{unsigned t}) (a b:uint_t t SEC) : Lemma
  (requires t =!= U1)
  (ensures v (logxor a b) == U.logxor #(bits t) (v a) (v b))

val define_eq_mask (t:inttype{unsigned t}) (a b:uint_t t SEC) : Lemma
  (v (eq_mask a b) == (if v a = v b then pow2 (bits t) - 1 else 0))
