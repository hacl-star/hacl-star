module Hacl.Argmax.Common

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Constructive
open FStar.Mul
open FStar.Calc


(* Primes and composite numbers *)

type big = x:int{x > 1}

val isprm: p:big -> bool
let isprm _ = magic()

type prm = n:big{isprm n}

val iscomp: n:big -> Type0
let iscomp n = exists (p:prm) (q:prm). n = p * q

type comp = n:big{iscomp n}

val one: pos
let one = 1

(* Basic algebra *)

val field_el: #n:big -> a:int -> bool
let field_el #n a = a >= 0 && a < n

type fe n = x:int{field_el #n x}

val to_fe: #n:big -> a:nat -> r:fe n
let to_fe #n a = lemma_mod_lt a n; a % n

type binop = #n:big -> fe n -> fe n -> fe n
val ( +% ): binop
val ( *% ): binop
let ( +% ) #n n1 n2 = (n1 + n2) % n
let ( *% ) #n n1 n2 = (n1 * n2) % n

val sqr: #n:big -> fe n -> fe n
let sqr #n a = a *% a

val mul_one: #n:big -> a:fe n -> Lemma
  (ensures (a *% one = a /\ one *% a = a))
  [SMTPat (one *% a); SMTPat (a *% one)]
let mul_one #n a = ()

val mul_comm: #n:big -> a:fe n -> b:fe n -> Lemma
  (ensures (a *% b = b *% a))
  [SMTPat (a *% b)]
let mul_comm #n a b = ()

val modulo_mul_distributivity: a:int -> b:int -> n:pos ->
    Lemma ((a * b) % n = ((a % n) * (b % n)) % n)
let rec modulo_mul_distributivity a b n =
  lemma_mod_mul_distr_l a b n;
  lemma_mod_mul_distr_r (a % n) b n

val mod_twice: x:int -> n:pos -> Lemma
  ((x % n) % n = x % n)
let mod_twice _ _ = ()

val mul3_modulo_out_l: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a *% b) *% c = ((a * b) * c) % n)
let mul3_modulo_out_l #n a b c =
  calc (==) {
   (a *% b) *% c;
  == { }
   ( (a * b) % n ) *% c;
  == { }
   ( ((a * b) % n) * c ) % n;
  == { modulo_mul_distributivity ((a * b) % n) c n }
   ( (((a * b) % n) % n) * (c % n) ) % n;
  == { mod_twice (a * b) n }
   ( ((a * b) % n) * (c % n)) % n;
  == { modulo_mul_distributivity (a * b) c n }
   ( (a * b) * c ) % n;
  }

val mul3_modulo_out_r: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (a *% (b *% c) = (a * (b * c)) % n)
let mul3_modulo_out_r #n a b c =
  calc (==) {
    a *% (b *% c);
   == { mul3_modulo_out_l #n b c a }
    ((b * c) * a) % n;
   == { swap_mul (b * c) a }
    (a * (b * c)) % n;
  }

val mul_assoc: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (ensures ((a *% b) *% c = a *% (b *% c)))
  [SMTPat ((a *% b) *% c); SMTPat (a *% (b *% c))]
let mul_assoc #n a b c =
  calc (==) {
    (a *% b) *% c;
  == { mul3_modulo_out_l a b c }
    ((a * b) * c) % n;
  == { assert((a*b)*c = a*(b*c)) }
    (a * (b * c)) % n;
  == { mul3_modulo_out_r a b c }
    (a *% (b *% c));
  }

val mul4_assoc: #n:big -> a:fe n -> b:fe n -> c:fe n -> d:fe n -> Lemma
  ((a *% b) *% (c *% d) = (a *% c) *% (b *% d))
let mul4_assoc #n a b c d =
  calc (==) {
    (a *% b) *% (c *% d);
  == { }
    a *% (b *% (c *% d));
  == { }
    a *% ((b *% c) *% d);
  == { }
    a *% ((c *% b) *% d);
  == { }
    a *% (c *% (b *% d));
  == { }
    (a *% c) *% (b *% d);
  }


// Define fexp' for composite n and for unit g.
val fexp: #n:big -> fe n -> e:nat -> Tot (fe n) (decreases e)
let rec fexp #n g e =
  if e = 1 then g
  else if e = 0 then 1
  else
     if e % 2 = 0
     then fexp (g *% g) (e / 2)
     else fexp (g *% g) ((e - 1) / 2) *% g

val fexp_mul1: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (fexp g e1 *% fexp g e2 = fexp g (e1 + e2))
let rec fexp_mul1 #n g e1 e2 = match e2 with
  | 0 -> ()
//  | 1 -> ()
  | _ -> admit()

val fexp_mul2: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (fexp (g1 *% g2) e = fexp g1 e *% fexp g2 e)
let fexp_mul2 #n _ _ _ = admit()

val fexp_exp: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (fexp #n (fexp #n g e1) e2 = fexp #n g (e1 * e2))
let fexp_exp #n _ _ _ = admit()

val fexp_one1: #n:big -> g:fe n -> Lemma
  (ensures (fexp g one = g))
  [SMTPat (fexp g one)]
let fexp_one1 #n _ = ()

val fexp_one2: #n:big -> e:nat -> Lemma
  (ensures (fexp #n one e = one))
  [SMTPat (fexp #n one e)]
let rec fexp_one2 #n e = match e with
  | 0 -> ()
  | _ ->  fexp_one2 #n (if e % 2 = 0 then e / 2 else (e - 1) / 2)

(* GCD and LCM *)

type divides (a:pos) (b:pos) = cexists (fun (c:pos) -> a * c == b)

type is_gcd (a:pos) (b:pos) (gcd:pos) =
    (forall (d:pos). divides d a /\ divides d b ==> divides d gcd)
    /\ divides gcd a
    /\ divides gcd b

val ex_eucl:
     a:pos
  -> b:pos
  -> r:tuple3 pos int int{ let (g,u,v) = r in is_gcd a b g /\ a * u + b * v = g }
let rec ex_eucl a b =
  admit();
  let (g,s,t) = ex_eucl (b % a) a in
  (g, t - (b / a) * s, s)

val gcd: a:pos -> b:pos -> Tot (r:pos{is_gcd a b r}) (decreases b)
let gcd a b = Mktuple3?._1 (ex_eucl a b)

val ex_eucl_lemma1: a:pos -> b:pos -> g:int -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = g))
  (ensures (exists k. gcd a b = k * g))
let ex_eucl_lemma1 a b g u v = admit()

val lcm: pos -> pos -> pos
let lcm a b = abs ((a / gcd a b) * b)

val mod_prop: n:big -> a:int -> b:int -> Lemma
  (requires (a % n = b))
  (ensures (a - b = (a / n) * n))
let mod_prop n a b =
  lemma_div_mod a n;
  assert(a % n = a - n * (a / n));
  assert(b = a - n * (a / n));
  assert(a - b = (a / n) * n)

val mod_ops_props1: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a +% b = c ==> (a + b) - c = ((a+b)/n) * n) /\
   (a *% b = c ==> (a * b) - c = ((a*b)/n) * n))
let mod_ops_props1 #n a b c =
  assert (a +% b = c ==> (mod_prop n (a+b) c; (a + b) - c = ((a+b)/n) * n));
  assert (a *% b = c ==> (mod_prop n (a*b) c; (a * b) - c = ((a*b)/n) * n))

val mod_ops_props2: #n:big -> a:fe n -> b:fe n -> c:fe n -> v:fe n -> Lemma
  (((a + b) - c = v * n ==> a +% b = c) /\
   ((a * b) - c = v * n ==> a *% b = c))
let mod_ops_props2 #n a b c v =

  multiple_modulo_lemma v n;
  assert((v * n) % n = 0);

  assert((a * b) - c = v * n ==> ((a * b) - c) % n = (v * n) % n);
  //assert((a * b) - c = v * n ==> ((a * b) - c) % n = 0);
  //assert((a * b) - c = v * n ==> (a * b) % n = c % n);
  //admit();
  //assert((a * b) - c = v * n ==> (a * b) % n = c);

//  admit();
//
//  let l1 (): Lemma ((a + b) - c = v * n ==> (a +% b) = c) =
//    (assert((a + b) - c = v * n ==> ((a + b) - c) % n = 0);
//     assert((a + b) - c = v * n ==> (a + b) % n = c % n);
//     assert((a + b) - c = v * n ==> (a + b) % n = c)) in
//
//  admit();


  admit()

(* Inverses *)

val isunit: #n:big -> a:fe n -> Type0
let isunit #n a = exists b. a *% b = 1

val finv0: #n:big -> a:fe n ->
  Tot (b:option (fe n){isunit a <==> (Some? b /\ Some?.v b *% a = one)})
let finv0 #n a = admit()

val finv: #n:big -> a:fe n{isunit a} -> b:fe n{b *% a = one}
let finv #n a = match finv0 a with | Some x -> x

val finv_unique: #n:big -> a:fe n -> b:fe n{b *% a = one} -> Lemma
  (isunit a /\ b = finv a)
let finv_unique #n a b =
  let z = finv a in
  calc (==) {
    z; =={} z *% one; =={} z *% (a *% b); =={}
            (z *% a) *% b; =={} one *% b; =={} b;
  }

val isunit_prod: #n:big -> a:fe n{isunit a} -> b:fe n{isunit b} -> Lemma
  (ensures (isunit (a *% b) /\ finv (a *% b) = finv a *% finv b))
let isunit_prod #n a b =
  mul4_assoc a b (finv a) (finv b);
  assert((a *% b) *% (finv a *% finv b) = one);
  finv_unique (a *% b) (finv a *% finv b)

val inv_as_gcd: #n:big -> a:fe n{a>0} -> Lemma
  (isunit a <==> gcd a n = 1)
let inv_as_gcd #n a =
  let (g,u,v) = ex_eucl a n in
  assert (gcd a n = g);
  assert (g = 1 ==> u*a + v*n = 1);
  assert (g = 1 ==> u*a - 1 = -v*n);
  assert (g = 1 ==> u*a - 1 = (-v)*n);
  assert (g = 1 ==> (u *% a) = 1);
  mod_ops_props #n
  admit()

val isunit_in_bigger: n1:big -> n2:big{n2 = (n2 / n1) * n1} -> a:fe n1{isunit a} -> Lemma
  (isunit (to_fe #n2 a))
let isunit_in_bigger n1 n2 a =
  let m = n2 / n1 in
  assert (n2 = m * n1);
  let b = finv a in
  assert (forall (c:fe n1{c > 1}).
          a *% b = c <==> (mod_ops_props a b c; a * b - c = ((a*b)/n1) * n1));
  assert (forall (c:fe n1{c > 1}).
          a *% b = c <==> (mod_ops_props a b c; m * ((a * b) - c) = m * ((a*b)/n1) * n1));
  assert (forall (c:fe n1{c > 1}).
          a *% b = c <==> (mod_ops_props a b c; m * ((a * b) - c) = ((a*b)/n1) * n2));
  assert (forall (c:fe n1{c > 1}).
          a *% b = c <==> (mod_ops_props a b c; m * (a * b) - m * c = ((a*b)/n1) * n2));
  assert (forall (c:fe n1{c > 1}).
          a *% b = c <==> (mod_ops_props a b c; m * (a * b) - m * c = ((a*b)/n1) * n2));
  assert (forall (c:fe n1{c > 1}).
          a *% b = c <==> (mod_ops_props a b c; m * (a * b) - m * c = ((a*b)/n1) * n2));

  admit ()
