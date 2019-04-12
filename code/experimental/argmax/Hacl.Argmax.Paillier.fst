module Hacl.Argmax.Paillier

open FStar.Mul

open Hacl.Argmax.Common


(* Internals *)

type fenu (n:comp) = r:fe n{isunit r}
type fen2 (n:comp) = fe (n * n)
type fen2u n = r:fen2 n{isunit r}

val in_base: #n:comp -> g:fe (n*n) -> Type0
let in_base #n g = exists (a:pos). b2t(fexp g (n * a) = 1)

type isg (n:comp) = g:fen2u n{in_base #n g}

// N plus one, for SMTPat not to throw warnings
val np1: #n:comp -> fen2 n
let np1 #n = 1 + n

val nplus1inbase: #n:comp -> Lemma
  (ensures (in_base (np1 #n) /\ isunit (np1 #n)))
  [SMTPat (np1 #n)]
let nplus1inbase #n = admit()


val encf: #n:comp -> g:isg n -> x:fe n -> y:fenu n -> fen2u n
let encf #n g x y =
  let r:fen2 n = fexp g x *% fexp (to_fe y) n in
  assume(isunit r);
  r

val is_res_class: #n:comp -> g:isg n -> w:fen2u n -> x:fe n -> Type0
let is_res_class #n g w x = exists y. encf g x y = w

// By bijectivity of encf with this specific g.
val ex_res_class: #n:comp -> g:isg n -> w:fen2u n -> Lemma
  (ensures (exists (x:fe n). is_res_class g w x))
let ex_res_class #n _ _ = admit()

val bigl:
     #n:comp
  -> u:fen2 n{u % n = 1}
  -> r:fe n{r = 0 <==> u = 1}
let bigl #n u = (u - 1) / n

// euler's totient
val etot: p:prm -> q:prm -> l:pos
let etot p q = lcm (p-1) (q-1)

val fltpq: p:prm -> q:prm -> w:fen2 (p*q) -> Lemma
  (ensures (let n = p*q in fexp w (etot p q) % n = 1))
  [SMTPat (fexp w (etot p q))]
let fltpq _ _ _ = admit()

// lemma 10 p227
val bigl_lemma1: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (ensures (let n = p * q in
            forall (x:fe n{is_res_class #n np1 w x}).
            let lm = etot p q in
            bigl (fexp w lm) = to_fe lm *% x))
let bigl_lemma1 _ _ _ = admit()

val bigl_lemma2: p:prm -> q:prm -> w:fen2u (p*q) -> g:isg (p*q) -> Lemma
  (ensures (let n = p * q in
            forall (c:fe n{is_res_class #n g w c})
                   (a:fe n{is_res_class #n np1 w a})
                   (b:fe n{is_res_class #n np1 g b}).
            isunit b /\ a *% finv b = c
            ))
let bigl_lemma2 _ _ _ _ = admit()

(* Keys *)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> g:isg (p*q)
         -> secret

type public =
  | Public: n:comp
         -> g:isg n
         -> public

val s2p: secret -> public
let s2p sec =
  Public (Secret?.p sec * Secret?.q sec)
         (Secret?.g sec)


(* Enc/Dec *)

type ciphertext (n:comp) = c:fen2u n

val encrypt:
     p:public
  -> r:pos{r < Public?.n p}
  -> m:fe (Public?.n p)
  -> ciphertext (Public?.n p)
let encrypt pub r m =
  admit();
  fexp (Public?.g pub) m *% fexp (to_fe r) (Public?.n pub)

#reset-options

val decrypt:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> m:fe (Public?.n (s2p s))
let decrypt sec c =
  let p = Secret?.p sec in
  let q = Secret?.q sec in
  let n = p * q in
  let g = Secret?.g sec in
  let lambda = etot p q in

  assume((fexp c lambda) % n = 1);
  let l1:fe n = bigl (fexp c lambda) in
  assume((fexp g lambda) % n = 1);
  let l2:fe n = bigl (fexp g lambda) in

  assume(isunit #n l2);
  let m = l1 *% finv l2 in
  m

#reset-options

val decryptExtra:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> Lemma
     (ensures
      (let n = Secret?.p s * Secret?.q s in
       forall (z:fe n{is_res_class #n (Secret?.g s) c z}).
       decrypt s c = z)
      )
let decryptExtra sec c =
  let p = Secret?.p sec in
  let q = Secret?.q sec in
  let n = p * q in
  let g = Secret?.g sec in
  let lambda = etot p q in
  let lambda' = to_fe lambda in

  assume((fexp c lambda) % n = 1);
  let l1:fe n = bigl (fexp c lambda) in
  bigl_lemma1 p q c;
  assert (forall (x:fe n{is_res_class #n np1 c x}). l1 = lambda' *% x);

  assume((fexp g lambda) % n = 1);
  let l2:fe n = bigl (fexp g lambda) in
  bigl_lemma1 p q g;
  assert (forall (y:fe n{is_res_class #n np1 g y}). l2 = lambda' *% y);

  bigl_lemma2 p q c g;

  assume(isunit #n lambda');
  // [g]_{1+n} = [1+n]_g^{-1}
  assume(forall (y:fe n{is_res_class #n np1 g y}). isunit y);

  assert (forall (y:fe n{is_res_class #n np1 g y}).
          (finv_comm2 lambda' y;
          finv l2 = finv lambda' *% finv y));
  // Our "forall" is "exists exactly one", but it should be
  // handled with care, b/c we can't now dedice the unit property
  // from what we have.
  assume(isunit l2);
  assert (forall (x:fe n{is_res_class #n np1 c x})
                 (y:fe n{is_res_class #n np1 g y}).
          l1 *% finv l2 = (lambda' *% x) *% (finv lambda' *% finv y));

  // tactics??
  assume(forall (a:fe n) b c d. (a *% b) *% (c *% d) = (a *% c) *% (b *% d));

  assert (forall (x:fe n{is_res_class #n np1 c x})
                 (y:fe n{is_res_class #n np1 g y}).
          l1 *% finv l2 = (lambda' *% finv lambda') *% (x *% finv y));

  assert (forall (x:fe n{is_res_class #n np1 c x})
                 (y:fe n{is_res_class #n np1 g y}).
          l1 *% finv l2 = 1 *% (x *% finv y));


  assert (forall (x:fe n{is_res_class #n np1 c x})
                 (y:fe n{is_res_class #n np1 g y}).
          l1 *% finv l2 = x *% finv y);

  bigl_lemma2 p q c g;

  assert (forall (z:fe n{is_res_class #n g c z})
                 (x:fe n{is_res_class #n np1 c x})
                 (y:fe n{is_res_class #n np1 g y}).
          l1 *% finv l2 = z);


  // Somehow we can't throw away unused forall variables :shrug:
  assume (forall (z:fe n{is_res_class #n g c z}).
          l1 *% finv l2 = z);

  let m = l1 *% finv l2 in

  assert(forall (z:fe n{is_res_class #n g c z}). m = z);

  assert(decrypt sec c = m)
