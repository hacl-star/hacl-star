module Hacl.Spec.HE.GM

open FStar.Mul
open FStar.Math.Lemmas

open Lib.Math.Algebra


(*** Squares and nonsquares ***)

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

(*** Legendre symbol ***)

val leg_symbol: a:nat -> p:prm -> res:int
let leg_symbol a p =
  let res = mexp (to_fe #p a) ((p-1)/2) in
  if res = p-1 then -1 else res

val leg_symbol_modulo: a:nat -> p:prm -> Lemma
  (leg_symbol (a % p) p = leg_symbol a p)
let leg_symbol_modulo a p = lemma_mod_twice a p

val leg_symbol_range_raw: #p:prm -> a:fe p -> Lemma
  (ensures (let l = leg_symbol a p in
            (a = 0 ==> l = 0) /\
            (a <> 0 ==> l = 1 \/ l = -1)))
let leg_symbol_range_raw #p a =
  let l = leg_symbol a p in
  assert (p >= 3);
  assert ((p-1)/2 <> 0);
  to_fe_idemp #p a;
  if a = 0
  then begin
    mexp_zero1 #p ((p-1)/2);
    lemma_mod_twice a p;
    assert (l = 0)
  end else begin
    flt #p a;
    lemma_div_exact (p-1) 2;
    mexp_exp a ((p-1)/2) 2;
    mexp_two_is_sqr #p (mexp a ((p-1)/2));
    assert (sqr (mexp a ((p-1)/2)) = 1);
    squares_of_one #p (mexp a ((p-1)/2));
    assert (l = 1 \/ l = -1)
  end

val leg_symbol_range: #p:prm -> a:fe p -> Lemma
  (ensures (let l = leg_symbol a p in (l = 1 \/ l = 0 \/ l = -1)))
let leg_symbol_range #p a = leg_symbol_range_raw a

val leg_symbol_range_exp: #p:prm -> a:fe p -> Lemma
  (requires (mexp (to_fe #p a) ((p-1)/2) <> p-1))
  (ensures (let res = mexp (to_fe #p a) ((p-1)/2) in res = 0 \/ res = 1))
let leg_symbol_range_exp #p a = leg_symbol_range a

val is_leg_symbol_raw: p:prm -> a:nat -> Lemma
  (ensures (let l = leg_symbol a p in
            let a' = to_fe #p a in
            (l = 1 \/ l = 0 \/ l = -1) /\
            (l = 1 <==> (is_sqr a' /\ a <> 0)) /\
            (l = (-1) <==> (is_nonsqr a' /\ a <> 0)) /\
            (l = 0 <==> a = 0)
            ))
let is_leg_symbol_raw _ _ = admit()

val is_leg_symbol: #p:prm -> a:fe p -> Lemma
  (ensures (let l = leg_symbol a p in
              (l = 1 \/ l = 0 \/ l = -1) /\
              (l = 1 <==> (is_sqr a /\ a <> 0)) /\
              (l = (-1) <==> (is_nonsqr a /\ a <> 0)) /\
              (l = 0 <==> a = 0)
              ))
let is_leg_symbol #p a = is_leg_symbol_raw p a; to_fe_idemp #p a

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
  mexp_mul2 a b ((p-1)/2);

  assert (mexp (a *% b) ((p-1)/2) = mexp a ((p-1)/2) *% mexp b ((p-1)/2));

  let l1 = leg_symbol a p in
  let l2 = leg_symbol b p in

  leg_symbol_range a;
  leg_symbol_range b;

  // conceptually easy, though we must check all the cases

  if l1 = 0 then mul_zero (mexp b ((p-1)/2)) else
  if l2 = 0 then mul_zero (mexp a ((p-1)/2)) else
  if l1 = -1 && l2 = -1 then begin
    to_fe_idemp #p (p-1);
    minus_one_square p;
    assert (mexp (a *% b) ((p-1)/2) = 1)
  end
  else if l1 = 1 && l2 = -1 then mul_one #p (mexp b ((p-1)/2))
  else if l1 = -1 && l2 = 1 then mul_one #p (mexp a ((p-1)/2))
  else mul_one #p (mexp a ((p-1)/2))

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


(*** Keys, enc/dec, hom props ***)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> y:fe (p * q){is_nonsqr (to_fe #p y) /\ is_nonsqr (to_fe #q y) /\ y % p <> 0 /\ y <> 0}
         -> secret

type public =
  | Public: n:comp
         -> y:fe n{is_nonsqr y /\ y <> 0}
         -> public

val s2p: secret -> public
let s2p sec =
  let p = Secret?.p sec in
  let q = Secret?.q sec in
  let y = Secret?.y sec in
  nonsq_mul_comp p q y;
  Public (p * q) y

type ciphertext (n:big) = c:fe n{c <> 0}

val encrypt_direct:
     n:big
  -> y:fe n
  -> r:fe n{sqr r > 0 /\ sqr r *% y > 0}
  -> m:bool
  -> c:ciphertext n
let encrypt_direct n y r m =
  let r' = sqr r in
  if m then r' *% y else r'

val encrypt:
     p:public
  -> r:fe (Public?.n p){sqr r > 0 /\ sqr r *% (Public?.y p) > 0}
  -> m:bool
  -> c:ciphertext (Public?.n p)
let encrypt p r m = encrypt_direct (Public?.n p) (Public?.y p) r m

val decrypt_direct: p:prm -> c:pos -> m:bool
let decrypt_direct p c =
  let v = leg_symbol c p in
  if v = 1 then false else true

val decrypt: s:secret -> c:ciphertext (Public?.n (s2p s)) -> m:bool
let decrypt s c = decrypt_direct (Secret?.p s) c

val hom_xor: #n:big -> c1:ciphertext n -> c2:ciphertext n{c1 *% c2 <> 0} -> c3:ciphertext n
let hom_xor #n c1 c2 = c1 *% c2

(*** Functional correctness, properties ***)

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

val enc_dec_id1:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> Lemma
  (requires (is_sqr c))
  (ensures (decrypt s c = false))
let enc_dec_id1 s c =
  sq_mul_comp (Secret?.p s) (Secret?.q s) c;
  is_leg_symbol_raw (Secret?.p s) c

val enc_dec_id2:
     s:secret
  -> a:fe (Public?.n (s2p s)){is_sqr a /\ a > 0}
  -> y:fe (Public?.n (s2p s)){is_nonsqr (to_fe #(Secret?.p s) y) /\ y > 0}
  -> Lemma
  (requires (a *% y <> 0))
  (ensures (decrypt s (a *% y) = true))
let enc_dec_id2 s a y =
  let p = Secret?.p s in
  let q = Secret?.q s in
  nat_times_nat_is_nat a y;
  leg_symbol_modulo (a * y) p;

  assert (leg_symbol ((a*y)%p) p = leg_symbol (a*y) p);
  leg_symbol_modulo a p;
  sq_mul_comp p q a;
  is_leg_symbol_raw p a;

  assert (leg_symbol a p = 1);

  leg_symbol_mul2 p a y;

  assert (leg_symbol (a * y) p = leg_symbol y p);

  is_leg_symbol_raw p y;
  assert (leg_symbol y p = -1);

  assert (leg_symbol (a * y) p = -1);

  modulo_modulo_lemma (a*y) p q;
  assert (leg_symbol (a *% y) p = -1)


val enc_dec_id:
     s:secret
  -> r:fe (Public?.n (s2p s)){sqr r <> 0 /\ sqr r *% (Secret?.y s) <> 0}
  -> m:bool
  -> Lemma
  // All these values are public, and p divides them with negligible prob
  // though how to express it better?
  (requires (let p = Secret?.p s in
             (encrypt (s2p s) r m) % p <> 0 /\
             (r * r) % p <> 0))
  (ensures (decrypt s (encrypt (s2p s) r m) = m))
let enc_dec_id sec r m =
  let pub = s2p sec in
  let n = Public?.n pub in
  let y: fe n = Public?.y pub in
  let c: ciphertext n = encrypt pub r m in

  if m then enc_dec_id2 sec (sqr r) y else enc_dec_id1 sec c


val xor: b1:bool -> b2:bool -> b3:bool
let xor b1 b2 = match (b1,b2) with
  | (false,false) -> false
  | (false,true) -> true
  | (true,false) -> true
  | (true,true) -> false

val bti: bool -> nat
let bti b = if b then 1 else 0

val enc_as_exp:
     p:public
  -> r:fe (Public?.n p){sqr r <> 0 /\ sqr r *% (Public?.y p) <> 0}
  -> m:bool
  -> Lemma (encrypt p r m = mexp (Public?.y p) (bti m) *% sqr r)
let enc_as_exp p r m =
  let y = Public?.y p in
  let c = encrypt p r m in
  if m then mexp_one1 y else (mexp_zero2 y; mul_one (sqr r))

val hom_xor_prop:
     s:secret
  -> r1:fe (Public?.n (s2p s)){sqr r1 <> 0 /\ sqr r1 *% (Secret?.y s) <> 0}
  -> r2:fe (Public?.n (s2p s)){sqr r2 <> 0 /\ sqr r2 *% (Secret?.y s) <> 0}
  -> m1:bool
  -> m2:bool
  -> Lemma
  (requires (encrypt (s2p s) r1 m1 *% encrypt (s2p s) r2 m2 <> 0 /\
             sqr (r1 *% r2) <> 0 /\
             sqr (r1 *% r2) *% (Secret?.y s) <> 0 /\
             ((r1 *% r2) * (r1 *% r2)) % (Secret?.p s) <> 0 /\
             encrypt (s2p s) (r1 *% r2) (xor m1 m2) % (Secret?.p s) <> 0))
  (ensures (let c1 = encrypt (s2p s) r1 m1 in
            let c2 = encrypt (s2p s) r2 m2 in
            decrypt s (hom_xor c1 c2) = xor m1 m2))
let hom_xor_prop s r1 r2 m1 m2 =
  let p = s2p s in
  let y = Public?.y p in
  let c1 = encrypt (s2p s) r1 m1 in
  let c2 = encrypt (s2p s) r2 m2 in
  enc_as_exp p r1 m1;
  enc_as_exp p r2 m2;
  mul4_assoc (mexp y (bti m1)) (sqr r1) (mexp y (bti m2)) (sqr r2);
  mul4_assoc r1 r1 r2 r2;
  mexp_mul1 y (bti m1) (bti m2);
  assert (hom_xor c1 c2 = mexp y (bti m1 + bti m2) *% sqr (r1 *% r2));

  if (m1 && m2) then begin
    assert (is_sqr (mexp y 2));
    assert (is_sqr (sqr (r1 *% r2)));
    assert (hom_xor c1 c2 = y *% y *% sqr (r1 *% r2));
    mul4_assoc y y (r1 *% r2) (r1 *% r2);
    assert (hom_xor c1 c2 = sqr (y *% r1 *% r2));
    assert (is_sqr (hom_xor c1 c2));
    enc_dec_id1 s (hom_xor c1 c2)
  end else begin
    assert (hom_xor c1 c2 = encrypt (s2p s) (r1 *% r2) (xor m1 m2));
    enc_dec_id s (r1 *% r2) (xor m1 m2)
  end
