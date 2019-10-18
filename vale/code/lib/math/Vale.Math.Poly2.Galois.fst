module Vale.Math.Poly2.Galois
open FStar.Mul

module U = FStar.UInt
module PL = Vale.Math.Poly2.Lemmas
module D = Vale.Math.Poly2.Defs_s
//module PD = Vale.Math.Poly2.Defs
module GI = Vale.Math.Poly2.Galois.IntTypes

// recursive definitions of from_vec/to_vec are prone to matching loops, so use no fuel from here on
#reset-options "--max_fuel 0 --max_ifuel 0"

let to_poly #f e =
  let G.GF t irred = f in
  let n = I.bits t in
  reverse (of_seq (U.to_vec #n (I.v e))) (n - 1)

let to_felem f p =
  let G.GF t irred = f in
  let n = I.bits t in
  let p = reverse p (n - 1) in
  Lib.IntTypes.Compatibility.nat_to_uint (U.from_vec #n (to_seq p n))

let lemma_to_poly_degree #f e =
  reveal_defs ()

let lemma_irred_degree f =
  let G.GF t irred = f in
  let n = I.bits t in
  PL.lemma_index_all ();
  PL.lemma_monomial_define n;
  PL.lemma_add_define_all ();
  PL.lemma_degree_is (irred_poly f) n;
  ()

let lemma_poly_felem f p =
  let G.GF t irred = f in
  let n = I.bits t in
  let r = reverse p (n - 1) in
  let s = to_seq r n in
  let u = U.from_vec #n s in
  let e = Lib.IntTypes.Compatibility.nat_to_uint u in
  let u' = I.v #t #I.SEC e in
  let s' = U.to_vec #n u' in
  let r' = of_seq s' in
  let p' = reverse r' (n - 1) in
  PL.lemma_index_all ();
  PL.lemma_reverse_define_all ();
  lemma_equal r r';
  lemma_equal p p';
  ()

let lemma_felem_poly #f e =
  let G.GF t irred = f in
  let n = I.bits t in
  let u = I.v #t #I.SEC e in
  let s = U.to_vec #n u in
  let r = of_seq s in
  let p = reverse r (n - 1) in
  let r' = reverse p (n - 1) in
  let s' = to_seq r' n in
  let u' = U.from_vec #n s' in
  let e' = Lib.IntTypes.Compatibility.nat_to_uint #t #I.SEC u' in
  PL.lemma_index_all ();
  PL.lemma_reverse_define_all ();
  lemma_equal r r';
  assert (equal s s');
  Lib.IntTypes.Compatibility.uintv_extensionality e e';
  ()

let lemma_zero f =
  let G.GF t irred = f in
  let n = I.bits t in
  let a = zero in
  let b = to_poly #f G.zero in
  let eq_i (i:int) : Lemma (a.[i] == b.[i]) =
    PL.lemma_index_all ();
    PL.lemma_reverse_define_all ();
    PL.lemma_zero_define ();
    (if 0 <= i && i < n then U.zero_to_vec_lemma #n (n - 1 - i));
    ()
    in
  PL.lemma_pointwise_equal a b eq_i

//let lemma_zero' (f:G.field) : Lemma
//  (G.zero == to_felem f zero)
//  =
//  lemma_zero f;
//  lemma_felem_poly #f G.zero

let lemma_one f =
  let G.GF t irred = f in
  let n = I.bits t in
  let a = one in
  let b = to_poly #f G.one in
  let eq_i (i:int) : Lemma (a.[i] == b.[i]) =
    PL.lemma_index_all ();
    PL.lemma_reverse_define_all ();
    PL.lemma_one_define ();
    (if 0 <= i && i < n then U.one_to_vec_lemma #n (n - 1 - i));
    ()
    in
  PL.lemma_pointwise_equal a b eq_i

let lemma_add f e1 e2 =
  let G.GF t irred = f in
  GI.define_logxor t e1 e2;
  PL.lemma_index_all ();
  PL.lemma_reverse_define_all ();
  PL.lemma_add_define_all ();
  lemma_equal (to_poly (G.fadd e1 e2)) (to_poly e1 +. to_poly e2)

let lemma_and f e1 e2 =
  let G.GF t irred = f in
  GI.define_logand t e1 e2;
  PL.lemma_index_all ();
  PL.lemma_reverse_define_all ();
  PL.lemma_and_define_all ();
  lemma_equal (to_poly (I.logand e1 e2)) (to_poly e1 &. to_poly e2)

let lemma_or f e1 e2 =
  let G.GF t irred = f in
  GI.define_logor t e1 e2;
  PL.lemma_index_all ();
  PL.lemma_reverse_define_all ();
  PL.lemma_or_define_all ();
  lemma_equal (to_poly (I.logor e1 e2)) (to_poly e1 |. to_poly e2)

let lemma_shift_left f e n =
  let G.GF t irred = f in
  let nf = I.bits t in
  PL.lemma_index_all ();
  PL.lemma_reverse_define_all ();
  PL.lemma_shift_define_all ();
  PL.lemma_mod_monomial (shift (to_poly e) (I.uint_v n)) nf;
  assert (I.uint_v (I.shift_left e n) == U.shift_left #nf (I.uint_v e) (I.uint_v n));
  lemma_equal (to_poly (I.shift_left e n)) (shift (to_poly e) (I.uint_v n) %. monomial (I.bits f.G.t))

let lemma_shift_right f e n =
  let G.GF t irred = f in
  let nf = I.bits t in
  PL.lemma_index_all ();
  PL.lemma_reverse_define_all ();
  PL.lemma_shift_define_all ();
  assert (I.uint_v (I.shift_right e n) == U.shift_right #nf (I.uint_v e) (I.uint_v n));
  lemma_equal (to_poly (I.shift_right e n)) (shift (to_poly e) (-(I.uint_v n)))

#reset-options

(*
Various definitions of multiply, ranging from Poly2 definition to GaloisField definition:
- Vale.Math.Poly2.Defs_s.mul
- mul_def: same as Defs_s.mul, but using abstract definition of poly
- pmul: equivalent to mul_def, but defined recursively based on adds and shifts by n
- mmul: same as pmul, but also do a "mod m" in the add
- smul: same as mmul, but incrementally shift by 1 rather than shifting by n and implement "mod m" using add
- gmul: same as fmul, but defined using recursion instead of repeati
- fmul: same as Spec.GaloisField.fmul, but use named function instead of lambda
- Spec.GaloisField.fmul
*)

let poly_length (p:poly) : nat =
  (if degree p < 0 then PL.lemma_degree_negative p);
  1 + degree p

unfold let sum_of_bools = D.sum_of_bools
let mul_element_fun (a b:poly) (k i:int) : bool = a.[i] && b.[k - i]

let mul_element (a b:poly) (k:int) : bool =
  sum_of_bools 0 (k + 1) (mul_element_fun a b k)

[@"opaque_to_smt"]
let mul_def (a b:poly) : Pure poly
  (requires True)
  (ensures fun p ->
    let len = poly_length a + poly_length b in
    poly_length p <= len /\
    (forall (i:nat).{:pattern p.[i]} i < len ==> p.[i] == mul_element a b i)
  )
  =
  let len = poly_length a + poly_length b in
  of_fun len (fun (i:nat) -> mul_element a b i)

let rec pmul_rec (a b:poly) (n:nat) : Tot poly (decreases n) =
  if n = 0 then zero
  else
    let n' = n - 1 in
    let p = pmul_rec a b n' in
    if b.[n'] then p +. shift a n' else p

let pmul (a b:poly) : poly =
  pmul_rec a b (poly_length b)

let rec mmul (a b m:poly) (n:nat) : Tot poly (decreases n) =
  if n = 0 then zero
  else
    let n' = n - 1 in
    let p = mmul a b m n' in
    if b.[n'] then p +. (shift a n' %. m) else p

let mod_bit1 (a m:poly) : poly =
  if a.[degree m] then a +. m else a

let rec smul_rec (a b m:poly) (n:nat) : Tot (poly & poly & poly) (decreases n) =
  if n = 0 then (zero, a, b)
  else
    let (p, a, b) = smul_rec a b m (n - 1) in
    let p = p +. (if b.[0] then a else zero) in
    let a = mod_bit1 (shift a 1) m in // mod_bit1 is equivalent to mod in this case
    let b = shift b (-1) in
    (p, a, b)

let smul (a b m:poly) (n:nat) : poly =
  let (p, _, _) = smul_rec a b m n in
  p

let mod_shift1 (a irred:poly) (k:nat) : poly =
  let s = shift a 1 %. monomial k in
  s +. (if a.[k - 1] then irred else zero)

let fmul_t (f:G.field) = G.felem f & G.felem f & G.felem f

let fmul_iter (f:G.field) : i:nat{i < I.bits f.G.t - 1} -> fmul_t f -> fmul_t f =
  fun i (p, a, b) ->
    let b0 = I.eq_mask #f.G.t (I.logand b (G.one #f)) (G.one #f) in
    let p = I.logxor p (I.logand b0 a) in
    let carry_mask = I.eq_mask #f.G.t (I.shift_right a (I.size (I.bits f.G.t - 1))) (G.one #f) in
    let a = I.shift_left a (I.size 1) in
    let a = I.logxor a (I.logand carry_mask f.G.irred) in
    let b = I.shift_right b (I.size 1) in
    (p, a, b)

let rec gmul_rec (f:G.field) (a b:G.felem f) (n:nat) : fmul_t f =
  if n = 0 then (G.zero #f, a, b)
  else
    let (p, a, b) = gmul_rec f a b (n - 1) in
    fmul_iter f 0 (p, a, b)

let gmul (f:G.field) (a b:G.felem f) : G.felem f =
  let (p, _, _) = gmul_rec f a b (I.bits f.G.t) in
  p

let fmul (f:G.field) (a b:G.felem f) : G.felem f =
  let one = G.one #f in
  let zero = G.zero #f in
  let (p, a, b) =
    Lib.LoopCombinators.repeati (I.bits f.G.t - 1)
    (fmul_iter f)
    (zero, a, b)
    in
  let b0 = I.eq_mask #f.G.t (I.logand b (G.one #f)) (G.one #f) in
  let p = I.logxor p (I.logand b0 a) in
  p

(*
Lemmas about multiplication
*)

let d (a:poly) : (b:D.poly{poly == D.poly /\ coerce D.poly a == b}) =
  reveal_defs ();
  Vale.Math.Poly2_s.to_poly a

let rec lemma_mul_element_rec (a b:poly) (k:int) (n:int) : Lemma
  (sum_of_bools 0 n (mul_element_fun a b k) == sum_of_bools 0 n (D.mul_element_fun (d a) (d b) k))
  =
  reveal_defs ();
  if n > 0 then lemma_mul_element_rec a b k (n - 1)

let lemma_mul_element (a b:poly) (k:int) : Lemma
  (mul_element a b k == D.mul_element (d a) (d b) k)
  =
  reveal_defs ();
  lemma_mul_element_rec a b k (k + 1);
  ()

let lemma_mul_def (a b:poly) : Lemma
  (mul_def a b == mul a b)
  =
  reveal_defs ();
  PL.lemma_pointwise_equal (mul_def a b) (mul a b) (lemma_mul_element a b)

let rec lemma_pmul_degree (a b:poly) (n:nat) : Lemma
  (requires True)
  (ensures poly_length (pmul_rec a b n) <= poly_length a + n)
  =
  if n > 0 then lemma_pmul_degree a b (n - 1)

let rec lemma_mul_pmul_k_base (a b:poly) (k:int) (n:nat) : Lemma
  (requires True)
  (ensures sum_of_bools 0 n (mul_element_fun a b k) == (pmul_rec b a n).[k])
  (decreases n)
  =
  PL.lemma_index_all ();
  PL.lemma_add_define_all ();
  PL.lemma_shift_define_all ();
  if n > 0 then lemma_mul_pmul_k_base a b k (n - 1)

let rec lemma_mul_pmul_k_left (a b:poly) (k:int) (n:nat) (n':int) : Lemma
  (requires k + 1 <= n' /\ n' <= n)
  (ensures sum_of_bools 0 n' (mul_element_fun a b k) == (pmul_rec b a n).[k])
  (decreases (n - n'))
  =
  PL.lemma_index_all ();
  PL.lemma_shift_define_all ();
  if n > n' then lemma_mul_pmul_k_left a b k n (n' + 1)
  else lemma_mul_pmul_k_base a b k n

let rec lemma_mul_pmul_k_right (a b:poly) (k:int) (n n':nat) : Lemma
  (requires n == poly_length a /\ n <= n')
  (ensures sum_of_bools 0 n' (mul_element_fun a b k) == (pmul_rec b a n).[k])
  (decreases n')
  =
  PL.lemma_index_all ();
  PL.lemma_shift_define_all ();
  if n' > n then lemma_mul_pmul_k_right a b k n (n' - 1)
  else lemma_mul_pmul_k_base a b k n

let lemma_mul_pmul_k (a b:poly) (k:int) : Lemma
  ((mul_def a b).[k] == (pmul b a).[k])
  =
  PL.lemma_index_all ();
  let n = poly_length a in
  lemma_pmul_degree b a n;
  if n = k + 1 then lemma_mul_pmul_k_base a b k n
  else if n > k + 1 then lemma_mul_pmul_k_left a b k n (k + 1)
  else lemma_mul_pmul_k_right a b k n (k + 1)

let lemma_mul_pmul (a b:poly) : Lemma
  (mul_def a b == pmul b a)
  =
  PL.lemma_pointwise_equal (mul_def a b) (pmul b a) (lemma_mul_pmul_k a b)

let rec lemma_mmul_pmul_rec (a b m:poly) (n:nat) : Lemma
  (requires poly_length m > 0)
  (ensures mod (mmul a b m n) m == mod (pmul_rec a b n) m)
  =
  if n > 0 then
  (
    let n' = n - 1 in
    let mp = mmul a b m n' in
    let pp = pmul_rec a b n' in
    lemma_mmul_pmul_rec a b m (n - 1);
    assert (mod mp m == mod pp m);
    let s = shift a n' in
    PL.lemma_mod_distribute pp s m;
    PL.lemma_mod_distribute mp s m;
    PL.lemma_mod_distribute mp (s %. m) m;
    PL.lemma_mod_mod s m;
    //assert ((mp +. (s %. m)) %. m == (mp +. s) %. m);
    //assert ((mp +. s) %. m == (pp +. s) %. m);
    //assert (mod (add mp (mod s m)) m == mod (add pp s) m);
    //assert (mod (add mp (mod (shift a n') m)) m == mod (add pp (shift a n')) m);
    ()
  )

let rec lemma_mmul_pmul (a b m:poly) (n:nat) : Lemma
  (requires poly_length m > 0 /\ n >= poly_length b)
  (ensures mod (mmul a b m n) m == mod (pmul a b) m)
  =
  PL.lemma_index_all ();
  if n = poly_length b then lemma_mmul_pmul_rec a b m n
  else lemma_mmul_pmul a b m (n - 1)

let lemma_mod_bit1 (a m:poly) : Lemma
  (requires poly_length a <= poly_length m /\ 0 <= degree m)
  (ensures mod_bit1 a m == a %. m)
  =
  PL.lemma_index_all ();
  PL.lemma_add_define_all ();
  let n = poly_length m in
  if (poly_length a < n) then PL.lemma_mod_small a m
  else
  (
    lemma_degree a;
    lemma_degree m;
    lemma_degree (a +. m);
    PL.lemma_mod_distribute a m m;
    PL.lemma_mod_cancel m;
    lemma_add_zero (a %. m);
    //assert ((a +. m) %. m == a %. m);
    PL.lemma_mod_small (a +. m) m;
    ()
  )

let lemma_mod_shift1 (a irred:poly) (k:nat) : Lemma
  (requires degree a < k /\ degree irred < k)
  (ensures mod_bit1 (shift a 1) (monomial k +. irred) == mod_shift1 a irred k /\ (shift a (1 - k) == one <==> a.[k - 1]))
  =
  let m = monomial k +. irred in
  let s = shift a 1 %. monomial k in
  PL.lemma_index_all ();
  PL.lemma_add_define_all ();
  PL.lemma_shift_define_all ();
  PL.lemma_monomial_define k;
  PL.lemma_one_define ();
  assert (m.[k]);
  PL.lemma_mod_monomial (shift a 1) k;
  if a.[k - 1] then
  (
    lemma_equal s (shift a 1 +. monomial k);
    lemma_equal (shift a 1 +. m) (s +. irred);
    ()
  )
  else
  (
    assert ((shift a (1 - k)).[0] == false);
    ()
  );
  lemma_equal (mod_bit1 (shift a 1) m) (mod_shift1 a irred k);
  if a.[k - 1] then lemma_equal (shift a (1 - k)) one;
  ()

let rec lemma_mmul_smul_rec (a b m:poly) (n:nat) : Lemma
  (requires degree m >= 0 /\ degree a < degree m)
  (ensures
    smul_rec a b m n == (mmul a b m n, shift a n %. m, shift b (-n)) /\
    mmul a b m n == mmul a b m n %. m
  )
  =
  PL.lemma_index_all ();
  PL.lemma_shift_define_all ();
  PL.lemma_mod_small a m;
  PL.lemma_mod_small zero m;
  lemma_equal (shift a 0) a;
  let (p0, a0, b0) = smul_rec a b m n in
  if n > 0 then
  (
    let n1 = n - 1 in
    let (p1, a1, b1) = smul_rec a b m n1 in
    lemma_mmul_smul_rec a b m n1;
    PL.lemma_shift_shift b (-n1) (-1);
    PL.lemma_shift_shift a n1 1;
    PL.lemma_shift_mod (shift a n1) m 1;
    PL.lemma_mod_distribute p1 a1 m;
    PL.lemma_mod_mod (shift a n1) m;
    lemma_mod_bit1 (shift a1 1) m;
    //assert ((p1 +. a1) %. m == p1 %. m +. a1 %. m);
    //assert ((p1 +. a1) %. m == p1 %. m +. (shift a n1 %. m));
    //assert ((p1 +. a1) %. m == p1 +. (shift a n1 %. m));
    lemma_add_zero p1;
    ()
  );
  lemma_equal b0 (shift b (-n));
  ()

let lemma_mmul_smul (a b m:poly) (n:nat) : Lemma
  (requires degree m >= 0 /\ degree a < degree m)
  (ensures smul a b m n == mmul a b m n)
  =
  lemma_mmul_smul_rec a b m n

let lemma_eqmask_and (t:I.inttype{Lib.IntTypes.unsigned t}) (a b c:I.uint_t t I.SEC) : Lemma
  (requires t =!= Lib.IntTypes.U1)
  (ensures I.v (I.logand (I.eq_mask a b) c) == (if I.v a = I.v b then I.v c else 0))
  =
  GI.define_eq_mask t a b;
  GI.define_logand t (I.eq_mask a b) c;
  U.logand_commutative #(I.bits t) (I.v (I.eq_mask a b)) (I.v c);
  U.logand_lemma_1 #(I.bits t) (I.v c);
  U.logand_lemma_2 #(I.bits t) (I.v c);
  ()

#reset-options "--z3rlimit 20"
let rec lemma_smul_gmul_rec (f:G.field) (e1 e2:G.felem f) (n:nat) : Lemma
  ( let (p, a, b) = gmul_rec f e1 e2 n in
    (to_poly p, to_poly a, to_poly b) == smul_rec (to_poly e1) (to_poly e2) (irred_poly f) n)
  =
  let G.GF t irred = f in
  let a = to_poly e1 in
  let b = to_poly e2 in
  let m = irred_poly f in
  lemma_zero f;
  lemma_one f;
  if n > 0 then
  (
    lemma_smul_gmul_rec f e1 e2 (n - 1);
    let (sp, sa, sb) = smul_rec a b m (n - 1) in
    let (gp, ga, gb) = gmul_rec f e1 e2 (n - 1) in
    //assert (to_poly gp == sp);
    //assert (to_poly ga == sa);
    //assert (to_poly gb == sb);

    let sp' = sp +. (if sb.[0] then sa else zero) in
    let sa' = mod_bit1 (shift sa 1) m in // mod_bit1 is equivalent to mod in this case
    let sb' = shift sb (-1) in
    let k = I.bits t in
    let m_lo = to_poly #f irred in
    lemma_mod_shift1 sa m_lo k;
    let ssa = shift sa 1 %. monomial k in
    let ssa_add = if sa.[k - 1] then m_lo else zero in
    let ssa' = ssa +. ssa_add in
    //assert (sa' == ssa');

    let gb0 = I.eq_mask #f.G.t (I.logand gb (G.one #f)) (G.one #f) in
    let gp' = I.logxor gp (I.logand gb0 ga) in
    let carry_mask = I.eq_mask #f.G.t (I.shift_right ga (I.size (I.bits f.G.t - 1))) (G.one #f) in
    let ga_shift = I.shift_left ga (I.size 1) in
    let carry_irred = I.logand carry_mask f.G.irred in
    let ga' = I.logxor ga_shift carry_irred in

    lemma_and f gb (G.one #f);
    lemma_felem_poly #f (I.logand gb (G.one #f));
    lemma_felem_poly #f G.one;
    PL.lemma_one_define ();
    PL.lemma_and_define_all ();
    if sb.[0] then lemma_equal (sb &. one) one;
    //assert (sb.[0] <==> I.v (I.logand gb (G.one #f)) = I.v (G.one #f));

    lemma_eqmask_and t (I.logand gb (G.one #f)) (G.one #f) ga;
    lemma_add f gp (I.logand gb0 ga);
    //assert (to_poly gp' == sp');

    let right_mask = I.shift_right ga (I.size (I.bits f.G.t - 1)) in
    lemma_eqmask_and t right_mask (G.one #f) f.G.irred;
    //assert (to_poly f.G.irred == m_lo);

    lemma_felem_poly right_mask;
    lemma_shift_right f ga (I.size (I.bits f.G.t - 1));
    //assert (to_poly carry_irred == ssa_add);
    lemma_add f ga_shift carry_irred;
    lemma_shift_left f ga (I.uint #I.U32 #I.PUB 1);
    //assert (to_poly ga_shift == ssa);
    //assert (to_poly ga' == ssa');

    let gb' = I.shift_right gb (I.size 1) in
    lemma_shift_right f gb (I.uint 1);
    //assert (to_poly gb' == sb');
    ()
  )

let lemma_smul_fmul (f:G.field) (e1 e2:G.felem f) : Lemma
  (to_poly (gmul f e1 e2) == smul (to_poly e1) (to_poly e2) (irred_poly f) (I.bits f.G.t))
  =
  let G.GF t irred = f in
  let n = I.bits t in
  lemma_smul_gmul_rec f e1 e2 n

let lemma_fmul_gmul (f:G.field) (a b:G.felem f) : Lemma
  (fmul f a b == gmul f a b)
  =
  let pred (n:nat) (pab:(fmul_t f)) : Type0 = gmul_rec f a b n == pab in
  let _ = Lib.LoopCombinators.repeati_inductive' (I.bits f.G.t - 1) pred (fmul_iter f) (G.zero #f, a, b) in
  ()

#reset-options "--initial_ifuel 1"
// HACK: It would be easier if G.fmul were already defined more like fmul (passing repeati a named function rather than a lambda)
let lemma_fmul_fmul (f:G.field) (a b:G.felem f) : Lemma
  (G.fmul a b == fmul f a b)
  =
  let repeati = Lib.LoopCombinators.repeati in
  let acc0 = (G.zero #f, a, b) in
  let rec lem (n:nat{n < I.bits f.G.t}) (f1:(i:nat{i < n} -> fmul_t f -> fmul_t f)) : Lemma
    (requires (forall (i:nat{i < n}) (pab:fmul_t f). f1 i pab == fmul_iter f i pab))
    (ensures repeati n (fmul_iter f) acc0 == repeati n f1 acc0)
    [SMTPat (repeati n f1 acc0)]
    =
    if n = 0 then
    (
      let pred (n:nat) (pab:(fmul_t f)) : Type0 = n == 0 ==> pab == acc0 in
      let _ = Lib.LoopCombinators.repeati_inductive' 0 pred (fmul_iter f) acc0 in
      let _ = Lib.LoopCombinators.repeati_inductive' 0 pred f1 acc0 in
      ()
    )
    else
    (
      lem (n - 1) f1;
      Lib.LoopCombinators.unfold_repeati n (fmul_iter f) acc0 (n - 1);
      Lib.LoopCombinators.unfold_repeati n f1 acc0 (n - 1);
      assert (repeati n (fmul_iter f) acc0 == repeati n f1 acc0);
      ()
    )
    in
  ()

#reset-options "--max_fuel 0 --max_ifuel 0"
let lemma_mul f a b =
  let G.GF t irred = f in
  let n = I.bits t in
  let pa = to_poly a in
  let pb = to_poly b in
  let m = irred_poly f in
  lemma_mul_commute pa pb;
  lemma_mul_def pb pa;
  lemma_mul_pmul pb pa;
  lemma_mmul_pmul pa pb m n;
  lemma_mmul_smul pa pb m n;
  lemma_smul_fmul f a b;
  lemma_fmul_gmul f a b;
  lemma_fmul_fmul f a b;
  PL.lemma_mod_small (to_poly (G.fmul a b)) m;
  ()
