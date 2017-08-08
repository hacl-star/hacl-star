module Hacl.Spec.BignumQ.Mul.Lemmas_1

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

open FStar.Mul

private
let lemma_distr_2_0 u x1 x2 : Lemma
  (u * (x1 + x2)
   == u * x1 + u * x2)
  = ()

private
let lemma_distr_3_0 u x1 x2 x3 : Lemma
  (u * (x1 + x2 + x3)
   == u * x1 + u * x2 + u * x3)
  = ()

private
let lemma_distr_4_0 u x1 x2 x3 x4 : Lemma
  (u * (x1 + x2 + x3 + x4)
   == u * x1 + u * x2 + u * x3 + u * x4)
  = ()

private
let lemma_distr_5_0 u x1 x2 x3 x4 x5 : Lemma
  (u * (x1 + x2 + x3 + x4 + x5)
   == u * x1 + u * x2 + u * x3 + u * x4 + u * x5)
  = ()

private
val lemma_mul_5:
  x1:int -> x2:int -> x3:int -> x4:int -> x5:int ->
  y1:int -> y2:int -> y3:int -> y4:int -> y5:int ->
  Lemma ((x1 + x2 + x3 + x4 + x5) * (y1 + y2 + y3 + y4 + y5)
    ==    x1 * y1
       +  x2 * y1 + x1 * y2
       +  x3 * y1 + x2 * y2 + x1 * y3
       +  x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4
       +  x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5
                 +  x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5
                           +  x5 * y3 + x4 * y4 + x3 * y5
                                     +  x5 * y4 + x4 * y5
                                               +  x5 * y5)
let lemma_mul_5 x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 =
  lemma_distr_5_0 (y1 + y2 + y3 + y4 + y5) x1 x2 x3 x4 x5;  
  lemma_distr_5_0 x1 y1  y2  y3  y4  y5;
  lemma_distr_5_0 x2 y1  y2  y3  y4  y5;
  lemma_distr_5_0 x3 y1  y2  y3  y4  y5;
  lemma_distr_5_0 x4 y1  y2  y3  y4  y5;
  lemma_distr_5_0 x5 y1  y2  y3  y4  y5

private
val lemma_mul_paren_4: a:int -> b:int -> c:int -> d:int -> Lemma ( (a * b) * (c * d) == (a * c) * (b * d))
let lemma_mul_paren_4 a b c d = ()

private
val lemma_mul_paren_3: a:int -> b:int -> c:int -> Lemma ( (a) * (b * c) == b * (a * c))
let lemma_mul_paren_3 a b c = ()

private
val lemma_mul_paren_3': a:int -> b:int -> c:int -> Lemma ( (a * b) * c == a * (b * c))
let lemma_mul_paren_3' a b c = ()

val lemma_mul_5':
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
let lemma_mul_5' x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 =
  lemma_mul_5 x1 (pow2 56 * x2) (pow2 112 * x3) (pow2 168 * x4) (pow2 224 * x5)
             y1 (pow2 56 * y2) (pow2 112 * y3) (pow2 168 * y4) (pow2 224 * y5);
  assert(x1 * y1
       +  (pow2 56 * x2) * y1 + x1 * (pow2 56 * y2)
       +  (pow2 112 * x3) * y1 + (pow2 56 * x2) * (pow2 56 * y2) + x1 * (pow2 112 * y3)
       +  (pow2 168 * x4) * y1 + (pow2 112 * x3) * (pow2 56 * y2) + (pow2 56 * x2) * (pow2 112 * y3) + x1 * (pow2 168 * y4)
       +  (pow2 224 * x5) * y1 + (pow2 168 * x4) * (pow2 56 * y2) + (pow2 112 * x3) * (pow2 112 * y3) + (pow2 56 * x2) * (pow2 168 * y4) + x1 * (pow2 224 * y5)
                 +  (pow2 224 * x5) * (pow2 56 * y2) + (pow2 168 * x4) * (pow2 112 * y3) + (pow2 112 * x3) * (pow2 168 * y4) + (pow2 56 * x2) * (pow2 224 * y5)
                           +  (pow2 224 * x5) * (pow2 112 * y3) + (pow2 168 * x4) * (pow2 168 * y4) + (pow2 112 * x3) * (pow2 224 * y5)
                                     +  (pow2 224 * x5) * (pow2 168 * y4) + (pow2 168 * x4) * (pow2 224 * y5)
                                               +  (pow2 224 * x5) * (pow2 224 * y5)
  == (x1 + pow2 56 * x2 + pow2 112 * x3 + pow2 168 * x4 + pow2 224 * x5)
         * (y1 + pow2 56 * y2 + pow2 112 * y3 + pow2 168 * y4 + pow2 224 * y5) );
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
  Math.Lemmas.pow2_plus 224 224;
  assert(x1 * y1
       +  (pow2 56 * x2) * y1 + x1 * (pow2 56 * y2)
       +  (pow2 112 * x3) * y1 + (pow2 56 * x2) * (pow2 56 * y2) + x1 * (pow2 112 * y3)
       +  (pow2 168 * x4) * y1 + (pow2 112 * x3) * (pow2 56 * y2) + (pow2 56 * x2) * (pow2 112 * y3) + x1 * (pow2 168 * y4)
       +  (pow2 224 * x5) * y1 + (pow2 168 * x4) * (pow2 56 * y2) + (pow2 112 * x3) * (pow2 112 * y3) + (pow2 56 * x2) * (pow2 168 * y4) + x1 * (pow2 224 * y5)
                 +  (pow2 224 * x5) * (pow2 56 * y2) + (pow2 168 * x4) * (pow2 112 * y3) + (pow2 112 * x3) * (pow2 168 * y4) + (pow2 56 * x2) * (pow2 224 * y5)
                           +  (pow2 224 * x5) * (pow2 112 * y3) + (pow2 168 * x4) * (pow2 168 * y4) + (pow2 112 * x3) * (pow2 224 * y5)
                                     +  (pow2 224 * x5) * (pow2 168 * y4) + (pow2 168 * x4) * (pow2 224 * y5)
                                               +  (pow2 224 * x5) * (pow2 224 * y5)
  == x1 * y1
       +  (pow2 56 * x2) * y1 + x1 * (pow2 56 * y2)
       +  (pow2 112 * x3) * y1 + pow2 112 * (x2 * y2) + x1 * (pow2 112 * y3)
       +  (pow2 168 * x4) * y1 + pow2 168 * (x3 * y2) + pow2 168 * (x2 * y3) + x1 * (pow2 168 * y4)
       +  (pow2 224 * x5) * y1 + pow2 224 * (x4 * y2) + pow2 224 * (x3 * y3) + pow2 224 * (x2 * y4) + x1 * (pow2 224 * y5)
                 +  pow2 280 * (x5 * y2) + pow2 280 * (x4 * y3) + pow2 280 * (x3 * y4) + pow2 280 * (x2 * y5)
                           +  pow2 336 * (x5 * y3) + pow2 336 * (x4 * y4) + pow2 336 * (x3 * y5)
                                     +  pow2 392 * (x5 * y4) + pow2 392 * (x4 * y5)
                                               +  pow2 448 * (x5 * y5) );
  lemma_mul_paren_3 x1 (pow2 56) (y2);
  lemma_mul_paren_3 x1 (pow2 112) (y3);
  lemma_mul_paren_3 x1 (pow2 168) (y4);
  lemma_mul_paren_3 x1 (pow2 224) (y5);
  lemma_mul_paren_3' (pow2 56)  (x2) y1;
  lemma_mul_paren_3' (pow2 112) (x3) y1;
  lemma_mul_paren_3' (pow2 168) (x4) y1;
  lemma_mul_paren_3' (pow2 224) (x5) y1

private
val lemma_mul_5'':
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
let lemma_mul_5'' x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 =
  lemma_mul_5' x1 x2 x3 x4 x5 y1 y2 y3 y4 y5;
  lemma_distr_2_0 (pow2 56) (x2 * y1) (x1 * y2);
  lemma_distr_2_0 (pow2 392) (x5 * y4) (x4 * y5);
  lemma_distr_3_0 (pow2 112) (x3 * y1) (x2 * y2) (x1 * y3);
  lemma_distr_3_0 (pow2 336) (x5 * y3) (x4 * y4) (x3 * y5);
  lemma_distr_4_0 (pow2 168) (x4 * y1) (x3 * y2) (x2 * y3) (x1 * y4);
  lemma_distr_4_0 (pow2 280) (x5 * y2) (x4 * y3) (x3 * y4) (x2 * y5);
  lemma_distr_5_0 (pow2 224) (x5 * y1) (x4 * y2) (x3 * y3) (x2 * y4) (x1 * y5)

private
val lemma_mul_5''':
  x1:nat -> x2:nat -> x3:nat -> x4:nat -> x5:nat ->
  y1:nat -> y2:nat -> y3:nat -> y4:nat -> y5:nat ->
  Lemma (((x1 + pow2 56 * x2 + pow2 112 * x3 + pow2 168 * x4 + pow2 224 * x5)
         * (y1 + pow2 56 * y2 + pow2 112 * y3 + pow2 168 * y4 + pow2 224 * y5)) % pow2 264
         ==
       (x1 * y1
       + pow2 56 * (x2 * y1 + x1 * y2)
       + pow2 112 * (x3 * y1 + x2 * y2 + x1 * y3)
       + pow2 168 * (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4)
       + pow2 224 * (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5)) % pow2 264)
let lemma_mul_5''' x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 =
  lemma_mul_5'' x1 x2 x3 x4 x5 y1 y2 y3 y4 y5;
  Math.Lemmas.pow2_plus 264 16;
  Math.Lemmas.pow2_plus 264 72;
  Math.Lemmas.pow2_plus 264 128;
  Math.Lemmas.pow2_plus 264 184;
  Math.Lemmas.paren_mul_right (pow2 264) (pow2 16) (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5);
  Math.Lemmas.paren_mul_right (pow2 264) (pow2 72) (x5 * y3 + x4 * y4 + x3 * y5);
  Math.Lemmas.paren_mul_right (pow2 264) (pow2 128) (x5 * y4 + x4 * y5);
  Math.Lemmas.paren_mul_right (pow2 264) (pow2 184) (x5 * y5);
  assert(x1 * y1
       + pow2 56 * (x2 * y1 + x1 * y2)
       + pow2 112 * (x3 * y1 + x2 * y2 + x1 * y3)
       + pow2 168 * (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4)
       + pow2 224 * (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5)
       + pow2 280 * (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5)
       + pow2 336 * (x5 * y3 + x4 * y4 + x3 * y5)
       + pow2 392 * (x5 * y4 + x4 * y5)
       + pow2 448 * (x5 * y5) ==
       x1 * y1
       + pow2 56 * (x2 * y1 + x1 * y2)
       + pow2 112 * (x3 * y1 + x2 * y2 + x1 * y3)
       + pow2 168 * (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4)
       + pow2 224 * (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5)
       + pow2 264 * (pow2 16 * (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5))
       + pow2 264 * (pow2 72 * (x5 * y3 + x4 * y4 + x3 * y5))
       + pow2 264 * (pow2 128 * (x5 * y4 + x4 * y5))
       + pow2 264 * (pow2 184 * (x5 * y5)));
  lemma_distr_4_0 (pow2 264) (pow2 16 * (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5))
                            (pow2 72 * (x5 * y3 + x4 * y4 + x3 * y5))
                            (pow2 128 * (x5 * y4 + x4 * y5))
                            (pow2 184 * (x5 * y5));
  assert(       x1 * y1
       + pow2 56 * (x2 * y1 + x1 * y2)
       + pow2 112 * (x3 * y1 + x2 * y2 + x1 * y3)
       + pow2 168 * (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4)
       + pow2 224 * (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5)
       + pow2 264 * (pow2 16 * (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5))
       + pow2 264 * (pow2 72 * (x5 * y3 + x4 * y4 + x3 * y5))
       + pow2 264 * (pow2 128 * (x5 * y4 + x4 * y5))
       + pow2 264 * (pow2 184 * (x5 * y5))
  ==   x1 * y1
       + pow2 56 * (x2 * y1 + x1 * y2)
       + pow2 112 * (x3 * y1 + x2 * y2 + x1 * y3)
       + pow2 168 * (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4)
       + pow2 224 * (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5)
       + pow2 264 * (pow2 16 * (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5) + pow2 72 * (x5 * y3 + x4 * y4 + x3 * y5) + pow2 128 * (x5 * y4 + x4 * y5) + (pow2 184 * (x5 * y5))));
  Math.Lemmas.lemma_mod_plus (x1 * y1
       + pow2 56 * (x2 * y1 + x1 * y2)
       + pow2 112 * (x3 * y1 + x2 * y2 + x1 * y3)
       + pow2 168 * (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4)
       + pow2 224 * (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5))
       ((pow2 16 * (x5 * y2 + x4 * y3 + x3 * y4 + x2 * y5)) +
                            (pow2 72 * (x5 * y3 + x4 * y4 + x3 * y5)) +
                            (pow2 128 * (x5 * y4 + x4 * y5)) +
                            (pow2 184 * (x5 * y5))) (pow2 264)


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

private let lemma_aux_0 (a:nat) (b:nat) (n:nat) : Lemma
  (pow2 n * a + pow2 (n+56) * b = pow2 n * (a % pow2 56) + pow2 (n+56) * (b + a / pow2 56))
  = Math.Lemmas.lemma_div_mod a (pow2 56);
    Math.Lemmas.pow2_plus n 56;
    assert(a = pow2 56 * (a / pow2 56) + (a % pow2 56));
    Math.Lemmas.distributivity_add_right (pow2 n) (pow2 56 * (a / pow2 56)) (a % pow2 56);
    cut (pow2 n * a = pow2 n * (pow2 56 * (a / pow2 56)) + pow2 n * (a % pow2 56));
    Math.Lemmas.paren_mul_right (pow2 n) (pow2 56) (a / pow2 56);
    Math.Lemmas.distributivity_add_right (pow2 (n+56)) b (a / pow2 56)

private
val lemma_mod_264:
  a0:nat -> a1:nat -> a2:nat -> a3:nat -> a4:nat ->
  Lemma ( (a0 + pow2 56 * a1 + pow2 112 * a2 + pow2 168 * a3 + pow2 224 * a4)
     = (a0 % pow2 56)
       + pow2 56 * ((a1 + (a0 / pow2 56)) % pow2 56)
       + pow2 112 * ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) % pow2 56)
       + pow2 168 * ((a3 + ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) / pow2 56)) % pow2 56)
       + pow2 224 * (a4 + ((a3 + ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) / pow2 56)) / pow2 56)))
let lemma_mod_264 a0 a1 a2 a3 a4 =
  Math.Lemmas.lemma_div_mod a0 (pow2 56);
  Math.Lemmas.distributivity_add_right (pow2 56) a1 (a0 / pow2 56);
  let a1':nat = (a1 + (a0 / pow2 56)) in
  let a2':nat = (a2 + (a1' / pow2 56)) in
  let a3':nat = (a3 + (a2' / pow2 56)) in
  lemma_aux_0 a1' a2 56;
  lemma_aux_0 a2' a3 112;
  lemma_aux_0 a3' a4 168

let u56 = a:nat{a < pow2 56}

private val lemma_mod_264'':
  a0:u56 -> a1:u56 -> a2:u56 -> a3:u56 -> a4:nat ->
  Lemma (a0 + pow2 56 * a1 + pow2 112 * a2 + pow2 168 * a3 + pow2 224 * (a4 % pow2 40) < pow2 264)
let lemma_mod_264'' a0 a1 a2 a3 a4 =
  assert_norm(pow2 40 = 0x10000000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 112 = 0x10000000000000000000000000000);
  assert_norm(pow2 168 = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224 = 0x100000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 264 = 0x1000000000000000000000000000000000000000000000000000000000000000000)


private val lemma_mod_264':
  a0:u56 -> a1:u56 -> a2:u56 -> a3:u56 -> a4:nat ->
  Lemma ((a0
       + pow2 56 * a1
       + pow2 112 * a2
       + pow2 168 * a3
       + pow2 224 * a4) % pow2 264 =
       a0
       + pow2 56 * a1
       + pow2 112 * a2
       + pow2 168 * a3
       + pow2 224 * (a4 % pow2 40) )
let lemma_mod_264' a0 a1 a2 a3 a4 =
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 112 = 0x10000000000000000000000000000);
  assert_norm(pow2 168 = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224 = 0x100000000000000000000000000000000000000000000000000000000);
  Math.Lemmas.lemma_mod_plus_distr_l (pow2 224 * a4) (a0 + pow2 56 * a1 + pow2 112 * a2 + pow2 168 * a3) (pow2 264);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 a4 264 224;
  lemma_mod_264'' a0 a1 a2 a3 a4;
  Math.Lemmas.modulo_lemma (a0 + pow2 56 * a1 + pow2 112 * a2 + pow2 168 * a3 + pow2 224 * (a4 % pow2 40)) (pow2 264)


private
val lemma_mod_264_:
  a0:nat -> a1:nat -> a2:nat -> a3:nat -> a4:nat ->
  Lemma ((a0 + pow2 56 * a1 + pow2 112 * a2 + pow2 168 * a3 + pow2 224 * a4) % pow2 264 =
       (a0 % pow2 56)
       + pow2 56 * ((a1 + (a0 / pow2 56)) % pow2 56)
       + pow2 112 * ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) % pow2 56)
       + pow2 168 * ((a3 + ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) / pow2 56)) % pow2 56)
       + pow2 224 * ((a4 + ((a3 + ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) / pow2 56)) / pow2 56)) % pow2 40))
let lemma_mod_264_ a0 a1 a2 a3 a4 =
  lemma_mod_264 a0 a1 a2 a3 a4;
  lemma_mod_264' (a0 % pow2 56) ((a1 + (a0 / pow2 56)) % pow2 56) ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) % pow2 56) ((a3 + ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) / pow2 56)) % pow2 56) (a4 + ((a3 + ((a2 + ((a1 + (a0 / pow2 56)) / pow2 56)) / pow2 56)) / pow2 56))


private let lemma_div_nat_is_nat (a:nat) (b:pos) : Lemma (a/b >= 0) = ()

val lemma_mul_5_low_264:
  x1:nat -> x2:nat -> x3:nat -> x4:nat -> x5:nat ->
  y1:nat -> y2:nat -> y3:nat -> y4:nat -> y5:nat ->
  Lemma (
    (x1 * y1) >= 0
    /\ (x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) >= 0
    /\ (x3 * y1 + x2 * y2 + x1 * y3 + ((x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) / pow2 56)) >= 0
    /\ (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4 + ((x3 * y1 + x2 * y2 + x1 * y3 + ((x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) / pow2 56)) / pow2 56)) >= 0
    /\ (
    let a0:nat = (x1 * y1) % pow2 56 in
    let a1:nat = ((x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) % pow2 56) in
    let a2 :nat = ((x3 * y1 + x2 * y2 + x1 * y3 + ((x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) / pow2 56)) % pow2 56) in
    let a3:nat = ((x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4 + ((x3 * y1 + x2 * y2 + x1 * y3 + ((x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) / pow2 56)) / pow2 56)) % pow2 56) in
    let a4:nat = (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5 + ((x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4 + ((x3 * y1 + x2 * y2 + x1 * y3 + ((x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) / pow2 56)) / pow2 56)) / pow2 56)) in
    ((x1 + pow2 56 * x2 + pow2 112 * x3 + pow2 168 * x4 + pow2 224 * x5)
         * (y1 + pow2 56 * y2 + pow2 112 * y3 + pow2 168 * y4 + pow2 224 * y5)) % pow2 264
    = a0 + pow2 56 * a1 + pow2 112 * a2 + pow2 168 * a3 + pow2 224 * (a4 % pow2 40)))
#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let lemma_mul_5_low_264 x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 =
  lemma_div_nat_is_nat (x1 * y1) (pow2 56);
  lemma_div_nat_is_nat (x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) (pow2 56);
  lemma_div_nat_is_nat (x3 * y1 + x2 * y2 + x1 * y3 + ((x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) / pow2 56)) (pow2 56);
  lemma_div_nat_is_nat (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4 + ((x3 * y1 + x2 * y2 + x1 * y3 + ((x2 * y1 + x1 * y2 + ((x1 * y1) / pow2 56)) / pow2 56)) / pow2 56)) (pow2 56);
  lemma_mul_5''' x1 x2 x3 x4 x5 y1 y2 y3 y4 y5;
  lemma_mod_264_ (x1 * y1) (x2 * y1 + x1 * y2) (x3 * y1 + x2 * y2 + x1 * y3) (x4 * y1 + x3 * y2 + x2 * y3 + x1 * y4) (x5 * y1 + x4 * y2 + x3 * y3 + x2 * y4 + x1 * y5)
