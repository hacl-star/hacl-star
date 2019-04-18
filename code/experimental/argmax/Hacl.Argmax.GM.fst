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
val leg_symbol: #n:big -> a:fe n -> res:int
let leg_symbol #n a = fexp a ((n-1)/2)

val is_leg_symbol: #n:big -> a:fe n -> Lemma
  (ensures (let l = leg_symbol a in
              (l = 1 \/ l = 0 \/ l = -1) /\
              (l = 1 <==> (is_sq a /\ a <> 0)) /\
              (l = (-1) <==> (is_nonsq a /\ a <> 0)) /\
              (l = 0 \/ b2t(a = 0))
              ))
  [SMTPat (leg_symbol a)]
let is_leg_symbol #n _ = admit()

val leg_symbol_prop1: #n:big -> a:fe n -> b:fe n -> Lemma
  (ensures (leg_symbol (a *% b) = leg_symbol a * leg_symbol b))
  [SMTPat (leg_symbol (a *% b))]
let leg_symbol_prop1 #n _ _ = admit()

val leg_symbol_prop2: p:prm -> q:prm -> a:fe (p * q) -> Lemma
  (ensures (leg_symbol a = leg_symbol #p (to_fe #p a) * leg_symbol #q (to_fe #q a)))
  [SMTPat (leg_symbol a)]
let leg_symbol_prop2 _ _ _ = admit()

val can_split_mul_sq: #n:comp -> a:fe n{is_sq a} -> b:fe n{b <> a && b <> 0} -> Lemma
  (ensures (is_sq (a *% b) ==> is_sq b))
let can_split_mul_sq #n a b =
  if a = 0 then () else
  assert(forall (x: fe n). leg_symbol x = 1 <==> (is_sq x /\ x <> 0));
  assert(is_sq (a *% b) ==> leg_symbol (a *% b) = 1);
  assert(is_sq (a *% b) ==> leg_symbol a * leg_symbol b = 1);
  assert(leg_symbol a = 1 \/ leg_symbol a = (-1));
  assert(leg_symbol b = 1 \/ leg_symbol b = (-1));
  assert(is_sq (a *% b) ==> (leg_symbol a = 1 /\ leg_symbol b = 1) \/
                           (leg_symbol a = (-1) /\ leg_symbol b = (-1)));
  assert(is_sq (a *% b) ==> (is_sq a /\ is_sq b) \/
                           (is_nonsq a /\ is_nonsq b));
  assert(is_sq (a *% b) ==> is_sq b)

val mul_sq_nonsq: #n:comp -> a:fe n{is_sq a} -> b:fe n{is_nonsq b} -> Lemma
  (ensures (is_nonsq (a *% b)))
let mul_sq_nonsq #n a b =
  nonsq_is_nonzero b;
  assert(~(exists s. b2t (sqr s = b)));
  assert((exists s. b2t (sqr s = b)) ==> false);
  can_split_mul_sq a b;
  assert(is_sq (a *% b) ==> is_sq b)

val nonsq_mul_comp: p:prm -> q:prm -> a:fe (p * q) -> Lemma
  (ensures (is_nonsq #p (to_fe a) /\ is_nonsq #q (to_fe a) ==> is_nonsq a))
let nonsq_mul_comp _ _ _ = admit()

(* Keys *)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> y:fe (p * q){is_nonsq y}
         -> secret

type public =
  | Public: n:comp
         -> y:fe n{is_nonsq y}
         -> public

val s2p: secret -> public
let s2p sec =
  Public (Secret?.p sec * Secret?.q sec)
         (Secret?.y sec)

(* Enc/Dec *)

type ciphertext (n:comp) = c:fe n{c > 0 && leg_symbol c <> 0}

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
  let v1 = leg_symbol #(Secret?.p s) (to_fe c) in
  let v2 = leg_symbol #(Secret?.q s) (to_fe c) in
  v1 = 1 && v2 = 1

val enc_dec_id:
     s:secret
  -> r:fe (Public?.n (s2p s)){sqr r > 0 /\ sqr r *% (Secret?.y s) > 0}
  -> m:bool
  -> Lemma
  (ensures (decrypt s (encrypt (s2p s) r m) = m))
let enc_dec_id sec r m =
  let pub = s2p sec in
  let p = Secret?.p sec in
  let q = Secret?.q sec in
  let n = Public?.n pub in
  let c = encrypt pub r m in
  assert(m <==> is_nonsq c);

  let d = decrypt sec c in
  let v1 = leg_symbol #p (to_fe c) in
  let v2 = leg_symbol #q (to_fe c) in

  assert(m ==> leg_symbol c = (-1));
  assert(m ==> (v1 = (-1) /\ v2 = 1) \/ (v1 = 1 /\ v2 = (-1)));
  assert(m ==> d = false);

  nonsq_mul_comp p q c;
  assert(not m ==> leg_symbol c = 1);
  assert(not m ==> (v1 = 1 /\ v2 = 1));
  assert(not m ==> d = true)
