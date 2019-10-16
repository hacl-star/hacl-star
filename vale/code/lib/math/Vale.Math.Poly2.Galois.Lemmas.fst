module Vale.Math.Poly2.Galois.Lemmas
open FStar.Mul
module PL = Vale.Math.Poly2.Lemmas

let lemma_eq_to_poly #f a b =
  lemma_felem_poly a;
  lemma_felem_poly b;
  ()

let lemma_mul_zero #f a =
  let pa = to_poly a in
  let m = irred_poly f in
  lemma_mul_zero pa;
  PL.lemma_mod_small zero m;
  lemma_eq_to_poly (fmul a G.zero) G.zero

let lemma_mul_one #f a =
  let pa = to_poly a in
  let m = irred_poly f in
  lemma_mul_one pa;
  PL.lemma_mod_small pa m;
  lemma_eq_to_poly (fmul a G.one) a

let lemma_mul_commute #f a b =
  let pa = to_poly a in
  let pb = to_poly b in
  let m = irred_poly f in
  lemma_mul_commute pa pb;
  lemma_eq_to_poly (fmul a b) (fmul b a)

let lemma_mul_associate #f a b c =
  let pa = to_poly a in
  let pb = to_poly b in
  let pc = to_poly c in
  let m = irred_poly f in
  lemma_mul_associate pa pb pc;
  // (((a * b) % m) * c) % m
  // (a * ((b * c) % m)) % m
  PL.lemma_mod_mul_mod (pa *. pb) m pc;
  PL.lemma_mod_mul_mod (pb *. pc) m pa;
  Vale.Math.Poly2.lemma_mul_commute pa (pb *. pc);
  Vale.Math.Poly2.lemma_mul_commute pa ((pb *. pc) %. m);
  lemma_eq_to_poly (fmul a (fmul b c)) (fmul (fmul a b) c)

let lemma_mul_distribute_left #f a b c =
  let pa = to_poly a in
  let pb = to_poly b in
  let pc = to_poly c in
  let m = irred_poly f in
  PL.lemma_mul_distribute_left pa pb pc;
  PL.lemma_mod_distribute (pa *. pc) (pb *. pc) m;
  lemma_eq_to_poly (fmul (fadd a b) c) (fadd (fmul a c) (fmul b c))

let lemma_mul_distribute_right #f a b c =
  lemma_mul_distribute_left b c a;
  // fmul (fadd b c) a == fadd (fmul b a) (fmul c a)
  lemma_mul_commute a b;
  lemma_mul_commute a c;
  lemma_mul_commute a (fadd b c);
  ()
