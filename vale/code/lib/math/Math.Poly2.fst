module Math.Poly2
module D = Math.Poly2.Defs_s
module I = Math.Poly2.Defs
open FStar.Seq
unfold let max = FStar.Math.Lib.max

let all_defs =
  poly == D.poly /\
  (forall (p:poly).{:pattern (degree p)} degree p == D.degree (to_poly p)) /\
  zero == of_poly D.zero /\
  one == of_poly D.one /\
  (forall (n:nat).{:pattern (monomial n)} monomial n == of_poly (D.monomial n)) /\
  (forall (p:poly) (n:int).{:pattern (shift p n)} shift p n == of_poly (D.shift (to_poly p) n)) /\
  (forall (p:poly) (n:nat).{:pattern (reverse p n)} reverse p n == of_poly (D.reverse (to_poly p) n)) /\
  (forall (p:poly) (n:int).{:pattern (poly_index p n)} poly_index p n == D.poly_index (to_poly p) n) /\
  (forall (a b:poly).{:pattern (add a b)} add a b == of_poly (D.add (to_poly a) (to_poly b))) /\
  (forall (a b:poly).{:pattern (mul a b)} mul a b == of_poly (D.mul (to_poly a) (to_poly b))) /\
  (forall (a b:poly).{:pattern (div a b)} degree b >= 0 ==> div a b == of_poly (D.div (to_poly a) (to_poly b))) /\
  (forall (a b:poly).{:pattern (mod a b)} degree b >= 0 ==> mod a b == of_poly (D.mod (to_poly a) (to_poly b)))

let reveal_all_defs : squash all_defs = reveal_defs ()

let poly_and a b = of_fun (1 + FStar.Math.Lib.max (size a) (size b)) (fun (i:nat) -> a.[i] && b.[i])
let poly_or a b = of_fun (FStar.Math.Lib.max (size a) (size b)) (fun (i:nat) -> a.[i] || b.[i])

let mask a n = of_fun n (fun (i:nat) -> a.[i])

let ones n = of_fun n (fun (i:nat) -> true)

let lemma_equal a b = I.lemma_poly_equal_elim (to_poly a) (to_poly b)
let lemma_index_i a i = ()
let lemma_degree a = ()

let lemma_zero_define_i i = ()
let lemma_one_define_i i = ()
let lemma_monomial_define_i n i = ()
let lemma_shift_define_i p n i = ()
let lemma_and_define_i a b i = ()
let lemma_or_define_i a b i = ()
let lemma_mask_define_i p n i = ()
let lemma_ones_define_i n i = ()
let lemma_reverse_define_i p n i = ()

let lemma_add_zero a = I.lemma_add_zero (to_poly a)
let lemma_add_cancel a = I.lemma_add_cancel (to_poly a)
let lemma_add_cancel_eq a b = I.lemma_add_cancel_eq (to_poly a) (to_poly b)
let lemma_add_commute a b = I.lemma_add_commute (to_poly a) (to_poly b)
let lemma_add_associate a b c = I.lemma_add_associate (to_poly a) (to_poly b) (to_poly c)
let lemma_add_define_i a b i = ()
let lemma_add_degree a b = ()

let lemma_mul_zero a = I.lemma_mul_zero (to_poly a)
let lemma_mul_one a = I.lemma_mul_one (to_poly a)
let lemma_mul_commute a b = I.lemma_mul_commute (to_poly a) (to_poly b)
let lemma_mul_associate a b c = I.lemma_mul_associate (to_poly a) (to_poly b) (to_poly c)
let lemma_mul_distribute a b c = I.lemma_mul_distribute (to_poly a) (to_poly b) (to_poly c)
let lemma_mul_degree a b = I.lemma_mul_degree (to_poly a) (to_poly b)
let lemma_mul_reverse a b n = I.lemma_mul_reverse (to_poly a) (to_poly b) n

let lemma_shift_is_mul a n = I.lemma_shift_is_mul (to_poly a) n

let lemma_div_mod a b = I.lemma_div_mod (to_poly a) (to_poly b)
let lemma_div_degree a b = I.lemma_div_degree (to_poly a) (to_poly b)
let lemma_mod_degree a b = I.lemma_mod_degree (to_poly a) (to_poly b)
