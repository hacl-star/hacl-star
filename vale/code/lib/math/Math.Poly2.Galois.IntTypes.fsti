module Math.Poly2.Galois.IntTypes
module U = FStar.UInt
open Lib.IntTypes

val define_logand (t:inttype) (a b:uint_t t SEC) : Lemma
  (v (logand a b) == U.logand #(bits t) (v a) (v b))

val define_logor (t:inttype) (a b:uint_t t SEC) : Lemma
  (v (logor a b) == U.logor #(bits t) (v a) (v b))

val define_logxor (t:inttype) (a b:uint_t t SEC) : Lemma
  (v (logxor a b) == U.logxor #(bits t) (v a) (v b))

val define_eq_mask (t:inttype) (a b:uint_t t SEC) : Lemma
  (v (eq_mask a b) == (if v a = v b then pow2 (bits t) - 1 else 0))
