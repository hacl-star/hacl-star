module Hacl.Argmax.Paillier

open FStar.Calc
open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Squash

open Hacl.Argmax.Common


(* Internals *)

type fenu (n:comp) = r:fe n{isunit r}
type fen2 (n:comp) = fe (n * n)
type fen2u n = r:fen2 n{isunit r}

// N plus one, for SMTPat not to throw warnings
val np1: #n:comp -> fen2 n
let np1 #n = 1 + n

val isunit_in_nsquare: #n:comp -> a:fe n{isunit a} -> Lemma
  (isunit (to_fe #(n*n) a))
let isunit_in_nsquare #n a = admit()

// euler's totient
val etot: p:prm -> q:prm -> l:fe (p*q)
let etot p q = lcm_less_mul (p-1) (q-1); lcm (p-1) (q-1)

// Because gcd (etot p q) (p*q) =
val etot_unit: p:prm -> q:prm -> Lemma
  (isunit #(p*q) (etot p q))
let etot_unit p q =
  let n = p*q in
  let lambda = etot p q in
  division_mul_after (p-1) (q-1) (gcd (p-1) (q-1));
  assert (lcm (p-1) (q-1) = ((p-1)*(q-1))/(gcd (p-1) (q-1)));
  assert (gcd n lambda = gcd n (lcm (p-1) (q-1)));
  // TODO
  admit()

val fltpq: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (ensures (let n = p*q in
            fexp w (etot p q) % n = 1 &&
            fexp w (etot p q) > 0))
let fltpq _ _ _ = admit()

val carmichael_thm: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (ensures (let l = etot p q in
            let n = p * q in
            fexp w (n*l) = one))
let carmichael_thm _ _ _ = admit()

// p225 after definition 1
val root_of_unity_form: #n:comp -> x:nat -> Lemma
  (fexp (np1 #n) x = 1 +% ((to_fe x) *% n))
let root_of_unity_form #n _ = admit()

val in_base_order: p:prm -> q:prm -> g:fe ((p*q)*(p*q)){isunit g} -> Type0
let in_base_order p q g =
  let r = mult_order g in
  let n = p * q in
  r % n = 0 /\ (r / n > 0) /\ (r / n < etot p q)

val in_base: p:prm -> q:prm -> g:fe ((p*q)*(p*q)) -> Type0
let in_base p q g = g <> 0 /\ isunit g /\ in_base_order p q g

val is_g: n:big -> g:fe (n*n) -> Type0
let is_g n g = isunit g /\ (exists (p:prm) (q:prm). n = p * q /\ in_base p q g)

type isg (n:big) = g:fe (n*n){is_g n g}

val np1_is_g: #n:comp -> Lemma (ensures (is_g n (np1 #n)))
let np1_is_g #n = admit()

val encf_raw: #n:comp -> g:isg n -> x:nat -> y:fenu n -> fen2 n
let encf_raw #n g x y = fexp g x *% fexp (to_fe y) n

val encf: #n:comp -> g:isg n -> x:fe n -> y:fenu n -> fen2 n
let encf #n g x y = fexp g x *% fexp (to_fe y) n

val encf_unit: #n:comp -> g:isg n -> x:fe n -> y:fenu n -> Lemma
  (isunit #(n*n) (encf #n g x y))
let encf_unit #n g x y =

  if x = 0 then (fexp_zero2 g; one_isunit n) else g_pow_isunit g x;
  assert(isunit (fexp g x));

  let y': fe (n*n) = to_fe y in
  isunit_in_nsquare #n y;

  g_pow_isunit y' n;
  // This is what g_pow_isunit proves, though assert lags a bit (?)
  assert(isunit (fexp y' n));

  isunit_prod (fexp g x) (fexp y' n)

// Injectiveness is proven at the page 226
// This "raw" version accounts for xs that are not in the field.
// The proof is exactly the same as in the paper.
val encf_inj_raw: #n:comp -> g:isg n -> x1:nat -> y1:fenu n -> x2:nat -> y2:fenu n -> Lemma
  (requires (encf_raw #n g x1 y1 = encf_raw #n g x2 y2))
  (ensures (to_fe #n x1 = to_fe #n x2 /\ y1 = y2))
let encf_inj_raw #n _ _ _ _ = admit()

val encf_inj: #n:comp -> g:isg n -> x1:fe n -> y1:fenu n -> x2:fe n -> y2:fenu n -> Lemma
  (requires (encf g x1 y1 = encf g x2 y2))
  (ensures (x1 = x2 /\ y1 = y2))
let encf_inj #n g x1 y1 x2 y2 =
  to_fe_idemp #n x1;
  to_fe_idemp #n x2;
  encf_inj_raw #n g x1 y1 x2 y2

// It is possible to get it checking every element of the preimage.
// encf is bijection for proper g
val encf_inv: #n:comp -> g:isg n -> w:fen2u n ->
  t:(tuple2 (fe n) (fenu n)){ encf g (fst t) (snd t) = w }
let encf_inv #n g w =
  if w = g
  then begin
    let x:fe (n*n) = one in
    let y:fe n = one in
    let y':fe (n*n) = one in

    fexp_one1 g;
    assert(fexp g one = g);
    fexp_one2 #(n*n) y;
    assert(fexp y' n = one);
    assert(fexp g one *% fexp y' n = g);
    assert(encf g x y = g);
    Mktuple2 x y
  end else admit() // it's hard to invert it

val is_res_class: #n:comp -> g:isg n -> w:fen2u n -> x:fe n -> Type0
let is_res_class #n g w x = exists y. encf g x y = w

val res_class: #n:comp -> g:isg n -> w:fen2u n -> x:fe n{is_res_class g w x}
let res_class #n g w = fst (encf_inv g w)

val res_class_decomposition: #n:comp -> g1:isg n -> g2:isg n ->  w:fen2u n -> Lemma
  (ensures (res_class g1 w = res_class g2 w *% res_class g1 g2))
let res_class_decomposition #n g1 g2 w =
  let (x1,y1) = encf_inv g1 w in
  let (x2,y2) = encf_inv g2 w in
  let (x3,y3) = encf_inv g1 g2 in
  let y2':fen2 n = to_fe #(n*n) y2 in
  let y3':fen2 n = to_fe #(n*n) y3 in

  nat_times_nat_is_nat x3 x2;
  nat_times_nat_is_nat n x2;

  let isunit_lemma1 (): Lemma (isunit (fexp y3 x2 *% y2)) = begin
    g_pow_isunit y3 x2;
    isunit_prod (fexp y3 x2) y2
    end in

  isunit_lemma1 ();

  // This property is easy to show, but it requires even more lemmas about
  // how exponentiation works.
  let l1 (): Lemma (fexp y3' x2 *% y2' = to_fe #(n*n) (fexp y3 x2 *% y2)) =
    assert (n >= 1);
    multiplication_order_lemma n 1 n;
    to_fe_bigger_and_back (n*n) y3;
    to_fe_bigger_and_back (n*n) y2;
    admit () in

  let encf_expand1 (): Lemma
      (encf_raw g1 x1 y1 =
       (fexp (fexp g1 x3 *% fexp y3' n) x2) *% fexp y2' n) =
    calc (==) {
      encf g1 x1 y1;
    == { }
      encf (encf g1 x3 y3) x2 y2;
    == { }
      encf (fexp g1 x3 *% fexp y3' n) x2 y2;
    == { }
      (fexp (fexp g1 x3 *% fexp y3' n) x2) *% fexp y2' n;
    } in

  let encf_expand2 (): Lemma
      (encf_raw g1 (x3 * x2) (fexp y3 x2 *% y2) =
       (fexp (fexp g1 x3 *% fexp y3' n) x2) *% fexp y2' n) = begin
    calc (==) {
      (fexp (fexp g1 x3 *% fexp y3' n) x2) *% fexp y2' n;
    == { fexp_mul2 (fexp g1 x3) (fexp y3' n) x2 }
      ((fexp (fexp g1 x3) x2) *% (fexp (fexp y3' n) x2)) *% fexp y2' n;
    == { fexp_exp g1 x3 x2 }
      (fexp g1 (x3 * x2) *% fexp (fexp y3' n) x2) *% fexp y2' n;
    == { }
      (fexp g1 (x3 * x2)) *% ((fexp (fexp y3' n) x2) *% fexp y2' n);
    == { fexp_exp y3' n x2 }
      (fexp g1 (x3 * x2)) *% (fexp y3' (n * x2) *% fexp y2' n);
    == { fexp_exp y3' x2 n }
      (fexp g1 (x3 * x2)) *% (fexp (fexp y3' x2) n *% fexp y2' n);
    == { fexp_mul2 (fexp y3' x2) y2' n }
      (fexp g1 (x3 * x2)) *% (fexp (fexp y3' x2 *% y2') n);
    == { l1 () }
      (fexp g1 (x3 * x2)) *% (fexp (to_fe (fexp y3 x2 *% y2)) n);
    == { }
      encf_raw g1 (x3 * x2) (fexp y3 x2 *% y2);
    }
    end in

  encf_expand1 ();
  encf_expand2 ();

  assert (encf_raw g1 x1 y1 = encf_raw g1 (x3 * x2) (fexp y3 x2 *% y2));

  encf_inj_raw g1 x1 y1 (x3 * x2) (fexp y3 x2 *% y2);
  to_fe_idemp #n x1;
  to_fe_mul' x3 x2;

  assert(x1 = x3 *% x2)


val res_class_inverse: #n:comp -> g1:isg n -> g2:isg n -> Lemma
  (isunit (res_class g1 g2) /\
   finv (res_class g1 g2) = res_class g2 g1)
let res_class_inverse #n g1 g2 =
  res_class_decomposition g1 g2 g1;
  assert(res_class g1 g1 = one);
  finv_unique (res_class g1 g2) (res_class g2 g1)

val bigl: #n:comp -> u:fen2 n{u > 0} -> r:fe n
let bigl #n u = (u - 1) / n

val bigl_prop: #n:comp -> u:fen2 n{u > 0} -> Lemma
  (ensures (let r = bigl u in u % n = 1 ==> (r = 0 <==> u = 1)))
let bigl_prop #n u =
  let r = bigl u in
  assert(u = 1 ==> r = 0);
  assert(u % n = 1 ==> (r = 0 ==> u = 1));
  assert(u % n = 1 ==> (r = 0 <==> u = 1))


val multiplication_order_lemma_strict: a:int -> b:int -> p:pos ->
    Lemma (a < b <==> a * p < b * p)
let multiplication_order_lemma_strict a b p = ()

val kn_mod_n2: #n:comp -> k:fe (n*n) -> Lemma
  (k *% n = (k % n) * n)
let kn_mod_n2 #n k =
  pos_times_pos_is_pos n n;
  let n2:pos = n * n in
  distributivity_add_left ((k/n)*n2) (k%n) n;
  assert(((k/n)*n + (k%n)) * n = (k/n)*n2 + (k%n)*n);
  assert((((k/n)*n + (k%n)) * n)%n2 = ((k/n)*n2 + (k%n)*n)%n2);
  modulo_distributivity ((k/n)*n2) ((k%n)*n) n2;
  cancel_mul_mod (k/n) n2;
  lemma_mod_twice ((k%n)*n) n;
  modulo_range_lemma k n;
  assert(k%n < n);
  multiplication_order_lemma_strict (k%n) n n;
  assert((k%n)*n < n*n);
  modulo_lemma ((k%n)*n) n2

val x_mod_n_limits: #n:comp -> x:nat -> Lemma
   (to_fe #(n*n) (1 + (x % n) * n) == 1 + (x % n) * n)
let x_mod_n_limits #n x =
  assert(1 + (x%n)*n < n*n);
  modulo_lemma (1+(x%n)*n) (n*n)

val roots_of_unity_mod_n: #n:comp -> x:nat -> Lemma
  (fexp (np1 #n) x = 1 + (x % n) * n)
let roots_of_unity_mod_n #n x =
  let n2 = n*n in
  root_of_unity_form #n x;
  x_mod_n_limits #n x;
  assert(to_fe #(n*n) (1 + (x % n) * n) == 1 + (x % n) * n);
  calc (==) {
    1 +% ((to_fe #n2 x) *% n);
  == { to_fe_add' 1 (to_fe #n2 x *% n) }
    to_fe (1 + ((to_fe #n2 x) *% n));
  == { to_fe_mul' (to_fe #n2 x) n }
    to_fe (1 + to_fe #n2 (to_fe #n2 x * n));
  == { }
    to_fe (1 + (x % n2 * n) % n2);
  == { kn_mod_n2 #n (x % n2) }
    to_fe (1 + ((x % n2) % n) * n);
  == { modulo_modulo_lemma x n n }
    to_fe #(n*n) (1 + (x % n) * n);
  == { }
    1 + (x % n) * n;
  }


val w_lambda_representation: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (let n = p * q in
   nplus1inbase #n;
   let a = res_class np1 w in
   let lm:fe n = etot p q in
   fexp w lm = 1 + ((a*lm)%n)*n)
let w_lambda_representation p q w =
  let n:comp = p * q in
  let lambda:pos = etot p q in
  nplus1inbase #n;
  let (a,b) = encf_inv (np1 #n) w in
  let b': fen2u n = isunit_in_nsquare b; to_fe b in
  assert (w = fexp (np1 #n) a *% fexp b' n);

  pos_times_pos_is_pos n lambda;
  nat_times_nat_is_nat a lambda;

  roots_of_unity_mod_n #n (a * lambda);
  assert (fexp (np1 #n) (a * lambda) = 1 + ((a*lambda) % n)*n);

  calc (==) {
    fexp w lambda;
  == { fexp_mul2 (fexp (np1 #n) a) (fexp b' n) lambda }
    (fexp (fexp np1 a) lambda) *% (fexp (fexp b' n) lambda);
  == { fexp_exp b' n lambda }
    (fexp (fexp np1 a) lambda) *% (fexp b' (n*lambda));
  == { carmichael_thm p q b' }
    fexp (fexp np1 a) lambda *% one;
  == { mul_one (fexp (fexp (np1 #n) a) lambda) }
    fexp (fexp np1 a) lambda;
  == { fexp_exp (np1 #n) a lambda }
    fexp (np1 #n) (a * lambda);
  == { }
    1 + ((a*lambda)%n)*n;
  }

// lemma 10 p227
val bigl_w_l_lemma: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (ensures (let n = p * q in
            nplus1inbase #n;
            let x = res_class np1 w in
            let lm:fe n = etot p q in
            fltpq p q w;
            bigl (fexp w lm) = lm *% x))
let bigl_w_l_lemma p q w =
  let n:comp = p * q in
  let lambda:fe n = etot p q in
  nplus1inbase #n;
  let a:fe n = res_class (np1 #n) w in
  w_lambda_representation p q w;

  let d:fen2 n = (1 + ((a * lambda) % n) * n) in
  assert(d > 0);

  calc (==) {
    bigl #n d;
  == { }
    (((a * lambda) % n) * n) / n;
  == { cancel_mul_div ((a * lambda) % n) n }
    (a * lambda) % n;
  == { to_fe_mul #n a lambda }
    to_fe #n a *% to_fe #n lambda;
  == { to_fe_idemp #n a }
    a *% to_fe lambda;
  == { to_fe_idemp #n lambda }
    a *% lambda;
  }

val l1_div_l2: p:prm -> q:prm -> w:fen2 (p*q) -> g:isg (p*q) -> fe (p*q)
let l1_div_l2 p q w g =
  let n = p * q in
  let lambda: fe n = etot p q in
  let l1arg = fexp w lambda in
  // If w is not guaranteed to be unit, then we could
  // possibly get 0, which is not a proper input to L.
  //
  // TODO decryption of non-units is nonstandard and should
  // be re-considered at some point.
  let l1:fe n = if l1arg = 0 then 0 else bigl l1arg in
  g_pow_isunit g lambda; isunit_nonzero (fexp g lambda);
  let l2:fe n = bigl (fexp g lambda) in

  l1 *% finv0 l2


val l1_div_l2_of_unit_w: p:prm -> q:prm -> w:fen2u (p*q) -> g:isg (p*q) -> Lemma
  (let lambda = etot p q in
   isunit (fexp w lambda) /\ (fexp w lambda > 0) /\
   isunit (fexp g lambda) /\ (fexp g lambda > 0) /\
   (isunit_nonzero (fexp g lambda);
    isunit (bigl (fexp g lambda))))
let l1_div_l2_of_unit_w p q w g =
  let n = p * q in
  let lambda:fe n = etot p q in
  let exp_is_unit (a:fen2u n): Lemma (isunit (fexp a lambda)) =
    begin
    g_pow_isunit a lambda;
    isunit_nonzero (fexp a lambda);
    assert (isunit (fexp a lambda))
    end in

  exp_is_unit w;
  exp_is_unit g;
  isunit_nonzero (fexp g lambda);

  let bigl_is_unit (): Lemma (isunit (bigl (fexp g lambda))) =
    begin
    nplus1inbase #n;
    bigl_w_l_lemma p q g;
    assert (bigl (fexp g lambda) = lambda *% res_class np1 g);
    etot_unit p q;
    res_class_inverse np1 g;
    isunit_prod lambda (res_class np1 g)
    end in

  bigl_is_unit ()


val fexp_w_lambda_is_one_mod_n: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (let lambda = etot p q in fexp w lambda % (p*q) = 1)
let fexp_w_lambda_is_one_mod_n p q w =
  let n:comp = p * q in
  one_mod_n n;
  let lambda:fe n = etot p q in
  nplus1inbase #n;
  let a:fe n = res_class (np1 #n) w in
  w_lambda_representation p q w;
  assert (fexp w lambda = 1 + ((a*lambda)%n)*n);
  assert (fexp w lambda % n = (1 + (((a*lambda)%n)*n))%n);
  modulo_distributivity 1 (((a*lambda)%n)*n) n;
  assert (fexp w lambda % n = (1%n + (((a*lambda)%n)*n)%n)%n);
  cancel_mul_mod ((a*lambda)%n) n;
  assert ((((a*lambda)%n)*n)%n = 0);
  assert (fexp w lambda % n = (1%n)%n);
  lemma_mod_twice 1 n;
  assert (fexp w lambda % n = 1)



val l1_div_l2_is_wg: p:prm -> q:prm -> w:fen2u (p*q) -> g:isg (p*q) -> Lemma
  (l1_div_l2 p q w g = res_class g w)
let l1_div_l2_is_wg p q w g =
  let n = p * q in
  let lambda: fe n = etot p q in

  nplus1inbase #n;
  let r_w = res_class #n np1 w in
  let r_g = res_class #n np1 g in
  let r_z = res_class #n g w in


  l1_div_l2_of_unit_w p q w g;
  let l1:fe n = bigl (fexp w lambda) in
  let l2:fe n = bigl (fexp g lambda) in

  fexp_w_lambda_is_one_mod_n p q w;
  fexp_w_lambda_is_one_mod_n p q g;

  bigl_prop (fexp w lambda);
  bigl_prop (fexp g lambda);

  bigl_w_l_lemma p q w;
  assert (l1 = lambda *% r_w);
  bigl_w_l_lemma p q g;
  assert (l2 = lambda *% r_g);

  res_class_decomposition (np1 #n) g w;
  assert (r_w = r_g *% r_z);

  res_class_inverse np1 g;

  finv_mul r_w r_g r_z;
  assert (r_w *% finv r_g = r_z);

  etot_unit p q;
  let lem1 (): Lemma (isunit l2 /\ finv l2 = finv lambda *% finv r_g) =
    isunit_prod lambda r_g in

  calc (==) {
    l1 *% finv l2;
   == { lem1 () }
    (lambda *% r_w) *% (finv lambda *% finv r_g);
   == { mul4_assoc lambda r_w (finv lambda) (finv r_g) }
    (lambda *% finv lambda) *% (r_w *% finv r_g);
   == { }
    one *% (r_w *% finv r_g);
   == { }
    r_w *% finv r_g;
   == { }
    r_z;
  }


(* Keys *)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> g:isg (p*q)
         -> secret

// TODO get rid of "comp" here
type public =
  | Public: n:comp
         -> g:isg n
         -> public

val s2p: secret -> public
let s2p sec =
  Public (Secret?.p sec * Secret?.q sec)
         (Secret?.g sec)


(* Enc/Dec *)

type ciphertext (n:comp) = c:fen2 n

// TODO get rid of assumes in the enc/dec, move it to lemmas

val encrypt:
     p:public
  -> r:fenu (Public?.n p)
  -> m:fe (Public?.n p)
  -> ciphertext (Public?.n p)
let encrypt pub r m = encf (Public?.g pub) m r

val decrypt:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> m:fe (Public?.n (s2p s))
let decrypt sec c = l1_div_l2 (Secret?.p sec) (Secret?.q sec) c (Secret?.g sec)

(* Functional correctness *)

val enc_is_unit:
     p:public
  -> r:fenu (Public?.n p)
  -> m:fe (Public?.n p)
  -> Lemma
  (isunit (encrypt p r m))
let enc_is_unit pub r m = encf_unit (Public?.g pub) m r

val decrypts_into_res_class:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> Lemma
     (requires (isunit c))
     (ensures (decrypt s c = res_class (Secret?.g s) c))
let decrypts_into_res_class sec c =
  l1_div_l2_is_wg (Secret?.p sec) (Secret?.q sec) c (Secret?.g sec)


val ex_ys: #n:comp -> g:isg n -> x1:fe n -> x2:fe n -> y1:fenu n -> y2:fenu n -> bool
let ex_ys #n g x1 x2 y1 y2 = encf g x1 y1 = encf g x2 y2


type y_pair (#n:comp) : Type = tuple2 (fenu n) (fenu n)

val exists_elim_pair (goal:Type) (#a:Type) (#p:(a -> a -> Type))
  (_:squash (exists (x:a) (y:a). p x y))
  (_:(x:a -> y:a{p x y} -> GTot (squash goal))) :Lemma goal
let exists_elim_pair goal #a #p have f =
  let joined1: squash (x:a & (exists (y:a). p x y)) = join_squash have in
  bind_squash #_ #goal joined1 (fun (| x, pf1 |) ->
    let joined2: squash (y:a & p x y) = join_squash (return_squash pf1) in
    bind_squash joined2 (fun (|y, pf2|) -> return_squash pf2; f x y))

val ex_pair: x:Type -> p:(x -> x -> bool) -> Lemma
  (requires (exists a b. p a b))
  (ensures (exists ab. p (fst ab) (snd ab)))
let ex_pair x p =
  let ex2: squash (exists (a:x) (b:x). p a b) = () in
  let goal = exists ab. p (fst ab) (snd ab) in
  exists_elim_pair
    goal
    ex2
    (fun a b -> let ab = Mktuple2 a b in assert(p (fst ab) (snd ab)))

val encf_inj_pair: #n:comp -> g:isg n -> x1:fe n -> x2:fe n -> Lemma
  (requires (exists y1 y2. encf g x1 y1 = encf g x2 y2))
  (ensures (x1 = x2))
let encf_inj_pair #n g x1 x2 =
  let ex_pair' y1 y2 = (encf g x1 y1 = encf g x2 y2) in

  let goal:Type = x1 = x2 in
  ex_pair (fenu n) ex_pair';
  let predicate (ys:y_pair):Type = ex_pair' (fst ys) (snd ys) in

  assert(exists (ys:y_pair #n). predicate ys);
  let ex: squash (exists (ys:y_pair #n). predicate ys) = () in

  let proof (ys:y_pair #n{predicate ys}): GTot (squash goal) =
    encf_inj g x1 (fst ys) x2 (snd ys) in

  exists_elim goal #(y_pair #n) #predicate ex proof

val enc_dec_id:
     s:secret
  -> r:fenu (Public?.n (s2p s))
  -> m:fe (Public?.n (s2p s))
  -> Lemma
  (ensures (decrypt s (encrypt (s2p s) r m) = m))
let enc_dec_id sec r m =
  let pub = s2p sec in
  let n = Public?.n pub in
  let g = Secret?.g sec in
  enc_is_unit pub r m;
  let c: fen2u n = encrypt (s2p sec) r m in
  assert(exists y1. encf g m y1 = c);
  let m' = decrypt sec c in
  let r_c = res_class g c in
  decrypts_into_res_class sec c;
  assert(r_c = m');

  assert(exists y1. encf g m y1 = c);
  assert(exists y2. encf g m' y2 = c);
  assert(exists y1 y2. encf g m y1 = encf g m' y2);
  encf_inj_pair g m m'
