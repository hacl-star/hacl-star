module Hacl.Spec.HE.GM

open FStar.Mul
open FStar.Math.Lemmas

open Lib.Math.Algebra


(* Squares and nonsquares *)

val is_sqr: #n:big -> a:fe n -> Type0
let is_sqr #n a = exists s . b2t(sqr s = a)

val is_nonsqr: #n:big -> a:fe n -> Type0
let is_nonsqr #n a = forall s. b2t(sqr s <> a)

val nonsq_is_nonzero: #n:big -> b:fe n{is_nonsqr b} -> Lemma (b <> 0)
let nonsq_is_nonzero #n b = ()

// This is a well-known fact, since we either have exactly two roots or none.
val squares_of_one: #p:prm -> a:fe p -> Lemma
  (requires (sqr a = 1))
  (ensures (a = 1 \/ a = p-1))
let squares_of_one #p _ = admit()

// These two lemmas cover quadratic residuosity modulo composite number
//
// For instance:
// https://en.wikipedia.org/wiki/Quadratic_residue#Composite_modulus_not_a_prime_power
// * residue => forall p^k residue
// * not residue => not (forall p^k residue)
// * not (forall p^k residue) => not residue (contraposition (1))
// * forall p^k residue => residue (contraposition (2))
val nonsq_mul_comp: p:prm -> q:prm -> a:fe (p * q) -> Lemma
  (requires (is_nonsqr #p (to_fe a)))
  (ensures (is_nonsqr a))
let nonsq_mul_comp _ _ _ = admit()

val sq_mul_comp: p:prm -> q:prm -> a:fe (p * q) -> Lemma
  (requires (is_sqr a))
  (ensures (is_sqr #p (to_fe a) /\ is_sqr #q (to_fe a)))
let sq_mul_comp _ _ _ = admit()

(* Legendre symbol *)

val leg_symbol: a:nat -> p:prm -> res:int
let leg_symbol a p =
  let res = fexp (to_fe #p a) ((p-1)/2) in
  if res = p-1 then -1 else res

val leg_symbol_modulo: a:nat -> p:prm -> Lemma
  (leg_symbol (a % p) p = leg_symbol a p)
let leg_symbol_modulo a p = lemma_mod_twice a p

val leg_symbol_range: #p:prm -> a:fe p -> Lemma
  (ensures (let l = leg_symbol a p in (l = 1 \/ l = 0 \/ l = -1)))
let leg_symbol_range #p a =
  let l = leg_symbol a p in
  assert (p >= 3);
  assert ((p-1)/2 <> 0);
  to_fe_idemp #p a;
  if a = 0
  then begin
    fexp_zero1 #p ((p-1)/2);
    lemma_mod_twice a p;
    assert (l = 0)
  end else begin
    flt #p a;
    lemma_div_exact (p-1) 2;
    fexp_exp a ((p-1)/2) 2;
    fexp_two_is_sqr #p (fexp a ((p-1)/2));
    assert (sqr (fexp a ((p-1)/2)) = 1);
    squares_of_one #p (fexp a ((p-1)/2));
    assert (l = 1 \/ l = -1)
  end

val is_leg_symbol: #p:prm -> a:fe p -> Lemma
  (ensures (let l = leg_symbol a p in
              (l = 1 \/ l = 0 \/ l = -1) /\
              (l = 1 <==> (is_sqr a /\ a <> 0)) /\
              (l = (-1) <==> (is_nonsqr a /\ a <> 0)) /\
              (l = 0 <==> a = 0)
              ))
let is_leg_symbol #p _ = admit()

#reset-options

val leg_of_fe_sqr: #p:prm -> a:fe p{sqr a <> 0} -> Lemma
  (leg_symbol (sqr a) p = 1)
let leg_of_fe_sqr #p a = is_leg_symbol (sqr a)

val leg_symbol_mul1: #p:prm -> a:fe p -> b:fe p -> Lemma
  (ensures (leg_symbol (a *% b) p = leg_symbol a p * leg_symbol b p))
let leg_symbol_mul1 #p a b =

  let goal = leg_symbol (a *% b) p = leg_symbol a p * leg_symbol b p in

  to_fe_idemp a;
  to_fe_idemp b;
  to_fe_idemp (a *% b);
  fexp_mul2 a b ((p-1)/2);

  assert (fexp (a *% b) ((p-1)/2) = fexp a ((p-1)/2) *% fexp b ((p-1)/2));

  let l1 = leg_symbol a p in
  let l2 = leg_symbol b p in

  leg_symbol_range a;
  leg_symbol_range b;

  // conceptually easy, though we must check all the cases

  if l1 = 0 then mul_zero (fexp b ((p-1)/2)) else
  if l2 = 0 then mul_zero (fexp a ((p-1)/2)) else
  if l1 = -1 && l2 = -1 then begin
    to_fe_idemp #p (p-1);
    minus_one_square p;
    assert (fexp (a *% b) ((p-1)/2) = 1)
  end
  else if l1 = 1 && l2 = -1 then mul_one #p (fexp b ((p-1)/2))
  else if l1 = -1 && l2 = 1 then mul_one #p (fexp a ((p-1)/2))
  else mul_one #p (fexp a ((p-1)/2))

val leg_symbol_mul2: p:prm -> a:nat -> b:nat -> Lemma
  (ensures (leg_symbol (a * b) p = leg_symbol a p * leg_symbol b p))
let leg_symbol_mul2 p a b =
  let a' = to_fe #p a in
  let b' = to_fe #p b in
  leg_symbol_mul1 a' b';
  leg_symbol_modulo (a * b) p;
  leg_symbol_modulo a p;
  leg_symbol_modulo b p;
  to_fe_mul #p a b


(* Keys *)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> y:fe (p * q){is_nonsqr (to_fe #p y) /\ is_nonsqr (to_fe #q y)}
         -> secret

type public =
  | Public: n:comp
         -> y:fe n{is_nonsqr y}
         -> public

val s2p: secret -> public
let s2p sec =
  let p = Secret?.p sec in
  let q = Secret?.q sec in
  let y = Secret?.y sec in
  nonsq_mul_comp p q y;
  Public (p * q) y

(* Enc/Dec *)

type ciphertext (n:comp) = c:fe n{c <> 0}

val encrypt:
     p:public
  -> r:fe (Public?.n p){sqr r > 0 /\ sqr r *% (Public?.y p) > 0}
  -> m:bool
  -> c:ciphertext (Public?.n p)
let encrypt p r m =
  let r' = sqr r in
  if m then r' *% (Public?.y p) else r'

val decrypt: s:secret -> c:ciphertext (Public?.n (s2p s)) -> m:bool
let decrypt s c =
  let v = leg_symbol c (Secret?.p s) in
  if v = 1 then false else true

(* Correctness *)

val sqr_mod_p_is_sqr: p:prm -> q:prm -> r:fe (p*q){(r * r) % p <> 0} -> Lemma
  (leg_symbol (sqr r) p = 1)
let sqr_mod_p_is_sqr p q r =
  let n = p * q in
  to_fe_mul #n r r;
  assert (sqr r = to_fe #n (r * r));
  leg_symbol_modulo (sqr r) p;
  assert (leg_symbol (sqr r) p = leg_symbol (((r * r)%n)%p) p);
  modulo_modulo_lemma (r * r) p q;
  leg_symbol_modulo (r * r) p;
  to_fe_mul #p r r;
  let r':fe p = to_fe r in
  assert (leg_symbol (sqr r) p = leg_symbol (sqr r') p);
  leg_of_fe_sqr r'

val enc_dec_id:
     s:secret
  -> r:fe (Public?.n (s2p s)){sqr r <> 0 /\ sqr r *% (Secret?.y s) <> 0}
  -> m:bool
  -> Lemma
  (ensures (decrypt s (encrypt (s2p s) r m) = m))
let enc_dec_id sec r m =
  let pub = s2p sec in
  let p = Secret?.p sec in
  let q = Secret?.q sec in
  let n = Public?.n pub in
  let y: fe n = Public?.y pub in
  let c: ciphertext n = encrypt pub r m in

  let c': fe p = to_fe #p c in

  // All these values are public, and p divides them with negligible prob
  // though how to express it without assumes?
  assume (c % p <> 0);
  assume (r * r % p <> 0);
  assume (y % p <> 0);

  let m' = decrypt sec c in

  let v = leg_symbol c' p in

  let mul_one (a:int): Lemma (1 * a = a) = () in

  let lemma_m_false (): Lemma (requires (not m)) (ensures (not m')) = begin
    sq_mul_comp p q c;
    is_leg_symbol c';
    leg_symbol_modulo c p
    end in

  let lemma_m_true (): Lemma (requires m) (ensures m') = begin
    nat_times_nat_is_nat (sqr r) y;
    leg_symbol_modulo (sqr r *% y) p;
    modulo_modulo_lemma (sqr r * y) p q;
    leg_symbol_modulo (sqr r * y) p;
    leg_symbol_mul2 p (sqr r) y;
    leg_symbol_modulo (sqr r) p;

    sqr_mod_p_is_sqr p q r;

    mul_one (leg_symbol y p);

    assert (leg_symbol (sqr r *% y) p = leg_symbol y p);

    is_leg_symbol #p (to_fe #p y);
    leg_symbol_modulo y p;

    assert (leg_symbol y p = -1)
    end in

  if m then lemma_m_true () else lemma_m_false ()
