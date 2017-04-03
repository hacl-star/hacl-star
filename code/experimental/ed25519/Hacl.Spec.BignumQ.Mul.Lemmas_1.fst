module Hacl.Spec.BignumQ.Mul.Lemmas

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

open FStar.Mul


(* private *)
(* let lemma_distr_5_0 u v x1 x2 x3 x4 x5 : Lemma *)
(*   (u * (x1 + v * x2 + v * v * x3 + v * v * v * x4 + v * v * v * v * x5) *)
(*    == u * x1 + v * u * x2 + v * v * u * x3 + v * v * v * u * x4 + v * v * v * v * u * x5) *)
(*   = () *)

(* private *)
(* let lemma_distr_5_1 u v x1 x2 x3 x4 x5 : Lemma *)
(*   (v * u * (x1 + v * x2 + v * v * x3 + v * v * v * x4 + v * v * v * v * x5) *)
(*    == v * u * x1 + v * v * u * x2 + v * v * v * u * x3 + v * v * v * v * u * x4 + v * v * v * v * v * u * x5) *)
(*   = () *)

(* private *)
(* let lemma_distr_5_2 u v x1 x2 x3 x4 x5 : Lemma *)
(*   (v * v * u * (x1 + v * x2 + v * v * x3 + v * v * v * x4 + v * v * v * v * x5) *)
(*    == v * v * u * x1 + v * v * v * u * x2 + v * v * v * v * u * x3 + v * v * v * v * v * u * x4 + v * v * v * v * v * v * u * x5) *)
(*   = lemma_distr_5_1 (v * u) v x1 x2 x3 x4 x5 *)

(* private *)
(* let lemma_distr_5_2 u v x1 x2 x3 x4 x5 : Lemma *)
(*   (v * v * u * (x1 + v * x2 + v * v * x3 + v * v * v * x4 + v * v * v * v * x5) *)
(*    == v * v * u * x1 + v * v * v * u * x2 + v * v * v * v * u * x3 + v * v * v * v * v * u * x4 + v * v * v * v * v * v * u * x5) *)
(*   = () *)

(* val lemma_mul_5: *)
(*   v:int -> *)
(*   x1:int -> x2:int -> x3:int -> x4:int -> x5:int -> *)
(*   y1:int -> y2:int -> y3:int -> y4:int -> y5:int -> *)
(*   Lemma ((x1 + v * x2 + v * v * x3 + v * v * v * x4 + v * v * v * v * x5) *)
(*          * (y1 + v * y2 + v * v * y3 + v * v * v * y4 + v * v * v * v * y5) *)
(*     == x1 * y1 *)
(*        + v * (x2 * y1 + x1 * y2) *)
(*        + v * v * (x3 * y1 + x2 * y2 + x1 * y3) *)
(*        + v * v * v * (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4) *)
(*        + v * v * v * v * (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5) *)
(*        + v * v * v * v * v * (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5) *)
(*        + v * v * v * v * v * v * (x5 * y3 + x4 * y4 + x3 * y5) *)
(*        + v * v * v * v * v * v * v * (x5 * y4 + x4 * y5) *)
(*        + v * v * v * v * v * v * v * v * (x5 * y5)) *)
(* let lemma_mul_5 v x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 = () *)

private
let lemma_distr_5_0 u x1 x2 x3 x4 x5 : Lemma
  (u * (x1 + x2 + x3 + x4 + x5)
   == u * x1 + u * x2 + u * x3 + u * x4 + u * x5)
  = ()

private
let lemma_distr_4_0 u x1 x2 x3 x4 : Lemma
  (u * (x1 + x2 + x3 + x4)
   == u * x1 + u * x2 + u * x3 + u * x4)
  = ()

private
let lemma_distr_3_0 u x1 x2 x3 : Lemma
  (u * (x1 + x2 + x3)
   == u * x1 + u * x2 + u * x3)
  = ()

private
let lemma_distr_2_0 u x1 x2 : Lemma
  (u * (x1 + x2)
   == u * x1 + u * x2)
  = ()

val lemma_mul_5:
  x1:int -> x2:int -> x3:int -> x4:int -> x5:int ->
  y1:int -> y2:int -> y3:int -> y4:int -> y5:int ->
  Lemma ((x1 + x2 + x3 + x4 + x5) * (y1 + y2 + y3 + y4 + y5)
    ==    x1 * y1
       + (x2 * y1 + x1 * y2)
       + (x3 * y1 + x2 * y2 + x1 * y3)
       + (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4)
       + (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5)
                 + (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5)
                           + (x5 * y3 + x4 * y4 + x3 * y5)
                                     + (x5 * y4 + x4 * y5)
                                               + (x5 * y5))
let lemma_mul_5 x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 =
  lemma_distr_5_0 (y1 + y2 + y3 + y4 + y5) x1 x2 x3 x4 x5;  
  lemma_distr_5_0 x1 y1  y2  y3  y4  y5;
  lemma_distr_5_0 x2 y1  y2  y3  y4  y5;
  lemma_distr_5_0 x3 y1  y2  y3  y4  y5;
  lemma_distr_5_0 x4 y1  y2  y3  y4  y5;
  lemma_distr_5_0 x5 y1  y2  y3  y4  y5


val lemma_mul_paren_4: a:int -> b:int -> c:int -> d:int -> Lemma ( (a * b) * (c * d) == (a * c) * (b * d))
let lemma_mul_paren_4 a b c d = ()

val lemma_mul_5':
  v:int ->
  x1:int -> x2:int -> x3:int -> x4:int -> x5:int ->
  y1:int -> y2:int -> y3:int -> y4:int -> y5:int ->
  Lemma ((x1 + pow2 56 * x2 + pow2 112 * x3 + pow2 168 * x4 + pow2 224 * x5)
         * (y1 + pow2 56 * y2 + pow2 112 * y3 + pow2 168 * y4 + pow2 224 * y5)
    == x1 * y1
       + pow2 56 * (x2 * y1) + pow2 56 * (x1 * y2)
       + pow2 112 * (x3 * y1) + pow2 112 * (x2 * y2) + pow2 112 * (x1 * y3)
       + pow2 168 * (x4 * y1) + pow2 168 * (x3 * y2) + pow2 168 * (x2 * y3) + pow2 168 * (x1 * y4)
       + pow2 224 * (x5 * y1) + pow2 224 * (x4 * y2) + pow2 224 * (x3 * y3) + pow2 224 * (x2 * y4) + pow2 224 * (x1 * y5)
       + pow2 280 * (x5 * y2) + pow2 280 * (x4 * y3) + pow2 280 * (x3 * y4) + pow2 280 * (x2 * y5)
       + pow2 336 * (x5 * y3) + pow2 336 * (x4 * y4) + pow2 336 * (x3 * y5)
       + pow2 392 * (x5 * y4) + pow2 392 * (x4 * y5)
       + pow2 448 * (x5 * y5))
let lemma_mul_5' v x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 =
  lemma_mul_5 x1 (pow2 56 * x2) (pow2 112 * x3) (pow2 168 * x4) (pow2 224 * x5)
             y1 (pow2 56 * y2) (pow2 112 * y3) (pow2 168 * y4) (pow2 224 * y5);
  lemma_mul_paren_4 (pow2 56)  x2 (pow2 56) (y2);
  lemma_mul_paren_4 (pow2 112) x3 (pow2 56) (y2);
  lemma_mul_paren_4 (pow2 168) x4 (pow2 56) (y2);
  lemma_mul_paren_4 (pow2 224) x5 (pow2 56) (y2);
  lemma_mul_paren_4 (pow2 56)  x2 (pow2 112) (y3);
  lemma_mul_paren_4 (pow2 112) x3 (pow2 112) (y3);
  lemma_mul_paren_4 (pow2 168) x4 (pow2 112) (y3);
  lemma_mul_paren_4 (pow2 224) x5 (pow2 112) (y3);
  lemma_mul_paren_4 (pow2 56)  x2 (pow2 168) (y4);
  lemma_mul_paren_4 (pow2 112) x3 (pow2 168) (y4);
  lemma_mul_paren_4 (pow2 168) x4 (pow2 168) (y4);
  lemma_mul_paren_4 (pow2 224) x5 (pow2 168) (y4);
  lemma_mul_paren_4 (pow2 56)  x2 (pow2 224) (y5);
  lemma_mul_paren_4 (pow2 112) x3 (pow2 224) (y5);
  lemma_mul_paren_4 (pow2 168) x4 (pow2 224) (y5);
  lemma_mul_paren_4 (pow2 224) x5 (pow2 224) (y5);
  Math.Lemmas.pow2_plus 56 56;
  Math.Lemmas.pow2_plus 56 112;
  Math.Lemmas.pow2_plus 56 168;
  Math.Lemmas.pow2_plus 56 224;
  Math.Lemmas.pow2_plus 112 56;
  Math.Lemmas.pow2_plus 112 112;
  Math.Lemmas.pow2_plus 112 168;
  Math.Lemmas.pow2_plus 112 224;
  Math.Lemmas.pow2_plus 168 56;
  Math.Lemmas.pow2_plus 168 112;
  Math.Lemmas.pow2_plus 168 168;
  Math.Lemmas.pow2_plus 168 224;
  Math.Lemmas.pow2_plus 224 56;
  Math.Lemmas.pow2_plus 224 112;
  Math.Lemmas.pow2_plus 224 168;
  Math.Lemmas.pow2_plus 224 224

val lemma_mul_5':
  v:int ->
  x1:int -> x2:int -> x3:int -> x4:int -> x5:int ->
  y1:int -> y2:int -> y3:int -> y4:int -> y5:int ->
  Lemma ((x1 + pow2 56 * x2 + pow2 112 * x3 + pow2 168 * x4 + pow2 224 * x5)
         * (y1 + pow2 56 * y2 + pow2 112 * y3 + pow2 168 * y4 + pow2 224 * y5)
    == x1 * y1
       + pow2 56 * (x2 * y1 + x1 * y2)
       + pow2 112 * (x3 * y1 + x2 * y2 + x1 * y3)
       + pow2 168 * (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4)
       + pow2 224 * (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5)
       + pow2 280 * (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5)
       + pow2 336 * (x5 * y3 + x4 * y4 + x3 * y5)
       + pow2 392 * (x5 * y4 + x4 * y5)
       + pow2 448 * (x5 * y5))
let lemma_mul_5' v x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 =
  lemma_mul_5 x1 (pow2 56 * x2) (pow2 112 * x3) (pow2 168 * x4) (pow2 224 * x5)
             y1 (pow2 56 * y2) (pow2 112 * y3) (pow2 168 * y4) (pow2 224 * y5);
  Math.Lemmas.pow2_plus 56 56;
  Math.Lemmas.pow2_plus 56 112;
  Math.Lemmas.pow2_plus 56 168;
  Math.Lemmas.pow2_plus 56 224;
  Math.Lemmas.pow2_plus 112 56;
  Math.Lemmas.pow2_plus 112 112;
  Math.Lemmas.pow2_plus 112 168;
  Math.Lemmas.pow2_plus 112 224;
  Math.Lemmas.pow2_plus 168 56;
  Math.Lemmas.pow2_plus 168 112;
  Math.Lemmas.pow2_plus 168 168;
  Math.Lemmas.pow2_plus 168 224;
  Math.Lemmas.pow2_plus 224 56;
  Math.Lemmas.pow2_plus 224 112;
  Math.Lemmas.pow2_plus 224 168;
  Math.Lemmas.pow2_plus 224 224;
  lemma_distr_2_0 (pow2 56)  (x2 * y1) (x1 * y2);
  lemma_distr_3_0 (pow2 112) (x3 * y1) (x2 * y2) (x1 * y3);
  lemma_distr_4_0 (pow2 168) (x4 * y1) (x3 * y2) (x2 * y3) (x1 * y4);
  lemma_distr_5_0 (pow2 224) (x5 * y1) (x4 * y2) (x3 * y3) (x2 * y4) (x1 * y5);
  lemma_distr_4_0 (pow2 280)           (x5 * y2) (x4 * y3) (x3 * y4) (x2 * y5);
  lemma_distr_3_0 (pow2 336)                     (x5 * y3) (x4 * y4) (x3 * y5);
  lemma_distr_2_0 (pow2 392)                               (x5 * y4) (x4 * y5)
