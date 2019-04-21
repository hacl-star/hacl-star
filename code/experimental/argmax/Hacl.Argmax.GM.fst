module Hacl.Argmax.GM

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Argmax.Common

(* Quadratic reciprocity *)

val is_sq: #n:big -> a:fe n -> Type0
let is_sq #n a = exists s . b2t(sqr s = a)

val is_nonsq: #n:big -> a:fe n -> Type0
let is_nonsq #n a = forall s. b2t(sqr s <> a)

val nonsq_is_nonzero: #n:big -> b:fe n{is_nonsq b} -> Lemma (b <> 0)
let nonsq_is_nonzero #n b = ()

// Legendre/Jacobi symbol
val leg_symbol: a:nat -> p:prm -> res:int
let leg_symbol a p =
  let res = fexp (to_fe #p a) ((p-1)/2) in
  if res = p-1 then -1 else res

val leg_symbol_modulo: a:nat -> p:prm -> Lemma
  (leg_symbol (a % p) p = leg_symbol a p)
let leg_symbol_modulo a p = lemma_mod_twice a p

val leg_symbol_range: #p:prm -> a:fe p -> Lemma
  (ensures (let l = leg_symbol a p in (l = 1 \/ l = 0 \/ l = -1)))
let leg_symbol_range #p _ = admit()

val is_leg_symbol: #p:prm -> a:fe p -> Lemma
  (ensures (let l = leg_symbol a p in
              (l = 1 \/ l = 0 \/ l = -1) /\
              (l = 1 <==> (is_sq a /\ a <> 0)) /\
              (l = (-1) <==> (is_nonsq a /\ a <> 0)) /\
              (l = 0 <==> a = 0)
              ))
let is_leg_symbol #p _ = admit()

#reset-options

val leg_of_fe_sqr: #p:prm -> a:fe p{a <> 0 /\ sqr a <> 0} -> Lemma
  (leg_symbol (sqr a) p = 1)
let leg_of_fe_sqr #p a = is_leg_symbol (sqr a)

val leg_symbol_prop1: #p:prm -> a:fe p -> b:fe p -> Lemma
  (ensures (leg_symbol (a *% b) p = leg_symbol a p * leg_symbol b p))
let leg_symbol_prop1 #p a b =
  to_fe_idemp a;
  to_fe_idemp b;
  fexp_mul2 a b ((p-1)/2);

  assert (fexp (a *% b) ((p-1)/2) = fexp a ((p-1)/2) *% fexp b ((p-1)/2));

  let l1 = leg_symbol a p in
  let l2 = leg_symbol b p in

  leg_symbol_range a;
  leg_symbol_range b;

  // conceptually easy, though we must check all the cases

  if l1 = -1 then
    assert (fexp a ((p-1)/2) = p - 1);
  if l2 = -1 then
    assert (fexp b ((p-1)/2) = p - 1);

  //if l1 = -1 && l2 = -1 then
  //  (minus_one_square p;
  //   assert (fexp a ((p-1)/2) *% fexp b ((p-1)/2) = 1));

  admit()

//val leg_symbol_prop2: p:prm -> q:prm -> a:nat -> Lemma
//  (ensures (leg_symbol a (p*q) = leg_symbol a p * leg_symbol a q))
//let leg_symbol_prop2 _ _ _ = admit()

val can_split_mul_sq: #n:comp -> a:fe n{is_sq a} -> b:fe n{b <> a && b <> 0} -> Lemma
  (ensures (is_sq (a *% b) ==> is_sq b))
let can_split_mul_sq #n a b = admit()
//  if a = 0 then admit() else
//  assert(forall (x: fe n). leg_symbol x = 1 <==> (is_sq x /\ x <> 0));
//  assert(is_sq (a *% b) ==> leg_symbol (a *% b) = 1);
//  assert(is_sq (a *% b) ==> leg_symbol a * leg_symbol b = 1);
//  assert(leg_symbol a = 1 \/ leg_symbol a = (-1));
//  assert(leg_symbol b = 1 \/ leg_symbol b = (-1));
//  assert(is_sq (a *% b) ==> (leg_symbol a = 1 /\ leg_symbol b = 1) \/
//                           (leg_symbol a = (-1) /\ leg_symbol b = (-1)));
//  assert(is_sq (a *% b) ==> (is_sq a /\ is_sq b) \/
//                           (is_nonsq a /\ is_nonsq b));
//  assert(is_sq (a *% b) ==> is_sq b)

val mul_sq_nonsq: #n:comp -> a:fe n{is_sq a} -> b:fe n{is_nonsq b} -> Lemma
  (ensures (is_nonsq (a *% b)))
let mul_sq_nonsq #n a b =
  nonsq_is_nonzero b;
  assert(~(exists s. b2t (sqr s = b)));
  assert((exists s. b2t (sqr s = b)) ==> false);
  can_split_mul_sq a b;
  assert(is_sq (a *% b) ==> is_sq b)

// https://en.wikipedia.org/wiki/Quadratic_residue#Composite_modulus_not_a_prime_power
// * residue => forall p^k residue
// * not residue => not (forall p^k residue)
// * not (forall p^k residue) => not residue (contraposition (1))
// * forall p^k residue => residue (contraposition (2))
val nonsq_mul_comp: p:prm -> q:prm -> a:fe (p * q) -> Lemma
  (requires (is_nonsq #p (to_fe a)))
  (ensures (is_nonsq a))
let nonsq_mul_comp _ _ _ = admit()

val sq_mul_comp: p:prm -> q:prm -> a:fe (p * q) -> Lemma
  (requires (is_sq a))
  (ensures (is_sq #p (to_fe a) /\ is_sq #q (to_fe a)))
let sq_mul_comp _ _ _ = admit()

(* Keys *)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> y:fe (p * q){is_nonsq (to_fe #p y) /\ is_nonsq (to_fe #q y)}
         -> secret

type public =
  | Public: n:comp
         -> y:fe n{is_nonsq y}
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

#reset-options

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

//  let c': fe p = to_fe #p c in
//  //let y': fe p = to_fe #p y in
//  //let rsq': fe p = to_fe #p (sqr r) in
//
//  let v = leg_symbol c p in
//  is_leg_symbol c';
//  //let m' = decrypt sec c in
//
//  //// it happens with negligible prob., though how to express it?
//  //assume (c' <> 0);
//
//  if m
//  then begin
//    //nat_times_nat_is_nat (sqr r) y;
//    //modulo_modulo_lemma (sqr r * y) p q;
//    //leg_symbol_modulo (sqr r *% y) p;
//    ////assert (leg_symbol (sqr r *% y) p = leg_symbol (sqr r * y) p);
//    //leg_symbol_prop1 p (sqr r) y;
//    //assert (leg_symbol (sqr r *% y) p = leg_symbol (sqr r) p * leg_symbol y p);
//    //assert (v = leg_symbol (sqr r) p * leg_symbol y p);
// //   to_fe_mul #p (sqr r) y;
// //   assert (to_fe #p (r' *% y) =
// //   //assert (leg_symbol (sqr r) = 1);
//    admit()
//  end else (sq_mul_comp p q c; assert (v = 1));

  admit()

  //assert(m ==> leg_symbol c = (-1));
  //assert(m ==> (v1 = (-1) /\ v2 = 1) \/ (v1 = 1 /\ v2 = (-1)));
  //assert(m ==> d = false);

  //nonsq_mul_comp p q c;
  //assert(not m ==> leg_symbol c = 1);
  //assert(not m ==> (v1 = 1 /\ v2 = 1));
  //assert(not m ==> d = true)
