module Hacl.Argmax.Common

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Constructive
open FStar.Classical
open FStar.Mul
open FStar.Calc


(* Divisibisity *)

type divides (a:pos) (b:pos) = b % a = 0

val modulo_mul_distributivity: a:int -> b:int -> n:pos ->
    Lemma ((a * b) % n = ((a % n) * (b % n)) % n)
let rec modulo_mul_distributivity a b n =
  lemma_mod_mul_distr_l a b n;
  lemma_mod_mul_distr_r (a % n) b n

val divides_multiple: a:pos -> b:pos{divides a b} -> k:pos -> Lemma
  (divides a (k*b))
let divides_multiple a b k = modulo_mul_distributivity k b a

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
  if a = 0 then (b, 0, 1) else
  let (g,s,t) = ex_eucl (b % a) a in
  (g, t - (b / a) * s, s)

val gcd: a:pos -> b:pos -> Tot (r:pos{is_gcd a b r}) (decreases b)
let gcd a b = Mktuple3?._1 (ex_eucl a b)

val ex_eucl_lemma1: a:pos -> b:pos -> g:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = g))
  (ensures (exists k. g = k * gcd a b))
let ex_eucl_lemma1 a b g u v = admit()

val ex_eucl_lemma2: a:pos -> b:pos -> g:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = g /\ divides g a /\ divides g b))
  (ensures (gcd a b = g))
let ex_eucl_lemma2 a b g u v = admit()

val ex_eucl_lemma3: a:pos -> b:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = 1))
  (ensures (gcd a b = 1))
let ex_eucl_lemma3 a b u v = ex_eucl_lemma2 a b 1 u v

val lcm: pos -> pos -> pos
let lcm a b = (a / gcd a b) * b

val division_mul_after: a:pos -> b:pos -> g:pos{divides g a} -> Lemma
  ((a / g) * b = (a * b) / g)
let division_mul_after a b g =
  assert (a % g = 0);
  assert (g * (a / g) = a);
  assert (g * ((a / g)*b) = a*b);

  divides_multiple g a b;
  assert ((a * b) % g = 0);
  assert (g * ((a * b) / g) = a*b)

val division_post_size: a:pos -> b:pos -> Lemma
  (a >= a / b)
let division_post_size a b = division_definition_lemma_1 a b a

val lcm_less_mul: a:pos -> b:pos -> Lemma
  (lcm a b <= a * b)
let lcm_less_mul a b =
  let g:pos = gcd a b in
  assert (lcm a b = (a / g) * b);
  division_mul_after a b g;
  assert (lcm a b = (a * b) / g);
  division_post_size (a * b) g

(* Numbers and elements *)

type big = x:int{x > 1}

val isprm: p:big -> bool
let isprm p = (p % 2 = 1 && p >= 3 && magic())

type prm = p:big{isprm p /\ (forall (x:nat{x>1&&x<p}). ~(divides x p)) }

val iscomp: n:big -> Type0
let iscomp n = exists (p:prm) (q:prm). n = p * q

type comp = n:big{iscomp n}

// In some cases F* can't decide the existential description
val mkcomp: p:prm -> q:prm -> comp
let mkcomp p q = p * q

val one: pos
let one = 1

val zero_mod_n: n:big -> Lemma (0 % n = 0)
let zero_mod_n _ = ()

val one_mod_n: n:big -> Lemma (1 % n = 1)
let one_mod_n _ = ()

val field_el: #n:big -> a:int -> bool
let field_el #n a = a >= 0 && a < n

type fe n = x:int{field_el #n x}

val to_fe: #n:big -> a:int -> r:fe n
let to_fe #n a = lemma_mod_lt a n; a % n

val to_fe_idemp: #n:big -> a:fe n -> Lemma
  (to_fe #n a = a)
let to_fe_idemp #n a = ()

(* Simplest functions and properties *)



(* Basic algebraic operations *)

type binop = #n:big -> fe n -> fe n -> fe n
val ( +% ): binop
let ( +% ) #n n1 n2 = (n1 + n2) % n

val neg: #n:big -> a:fe n -> r:fe n{a +% r = 0}
let neg #n a = if a = 0 then 0 else n - a

val ( -% ): binop
let ( -% ) #n n1 n2 = n1 +% neg n2

val ( *% ): binop
let ( *% ) #n n1 n2 = (n1 * n2) % n

val sqr: #n:big -> fe n -> fe n
let sqr #n a = a *% a

val minus_is_neg: a:nat -> n:big -> Lemma
  ((-(a % n)) % n = neg (to_fe #n a))
let minus_is_neg a n = ()

val to_fe_neg: #n:big -> a:nat -> Lemma
  ((-a)%n = neg (to_fe #n a))
let to_fe_neg #n a =
  lemma_div_mod a n;
  assert(a = (a/n)*n + a%n);
  assert(-a = -(a/n)*n -(a%n));
  assert((-a)%n = (-(a/n)*n -(a%n))%n);
  modulo_distributivity (-(a/n)*n) (-(a%n)) n;
  assert((-a)%n = ((-(a/n)*n)%n + (-(a%n))%n)%n);
  cancel_mul_mod (-(a/n)) n;
  assert((-a)%n = ((-(a%n))%n)%n);
  lemma_mod_twice (-(a%n)) n;
  assert((-a)%n = (-(a%n))%n);
  minus_is_neg a n

val to_fe_add: #n:big -> a:nat -> b:nat -> Lemma
  (to_fe #n (a + b) = to_fe a +% to_fe b)
let to_fe_add #n a b = modulo_distributivity a b n

val to_fe_add': #n:big -> a:fe n -> b:fe n -> Lemma
  (to_fe #n (a + b) = a +% b)
let to_fe_add' #n a b = to_fe_add #n a b

val to_fe_sub: #n:big -> a:nat -> b:nat -> Lemma
  (to_fe #n (a - b) = to_fe a -% to_fe b)
let to_fe_sub #n a b =
  modulo_distributivity a (-b) n;
  to_fe_neg #n b

val to_fe_sub': #n:big -> a:fe n -> b:fe n -> Lemma
  (to_fe #n (a - b) = a -% b)
let to_fe_sub' #n a b =
  to_fe_idemp a;
  to_fe_idemp b;
  to_fe_sub #n a b;
  assert (to_fe #n (a - b) = to_fe a -% to_fe b)

val to_fe_mul: #n:big -> a:nat -> b:nat -> Lemma
  (to_fe #n (a * b) = to_fe a *% to_fe b)
let to_fe_mul #n a b = modulo_mul_distributivity a b n

val to_fe_mul': #n:big -> a:fe n -> b:fe n -> Lemma
  (to_fe #n (a * b) = a *% b)
let to_fe_mul' #n a b = to_fe_mul #n a b

val minus_one_square: n:big -> Lemma
  (to_fe #n (n - 1) *% (n - 1) = 1)
let minus_one_square n =
  to_fe_mul #n (n - 1) (n - 1);
  assert ((n-1)*(n-1) = (n * n - 2 * n) + 1);
  modulo_distributivity (n * n - 2 * n) 1 n;
  modulo_distributivity (n * n) (-2 * n) n;
  assert (((n-1)*(n-1))%n = (((n*n)%n + ((-2)*n)%n)%n + 1%n)%n);
  cancel_mul_mod n n;
  cancel_mul_mod (-2) n;
  assert (((n-1)*(n-1))%n = ((0 + 0)%n + 1%n)%n);
  zero_mod_n n;
  assert (((n-1)*(n-1))%n = (1%n)%n);
  lemma_mod_twice 1 n;
  one_mod_n n

val add_move_to_right: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (requires (a -% b = c))
  (ensures (a = c +% b))
let add_move_to_right #n a b c =
  to_fe_sub' a b;
  assert (to_fe #n (a - b) = a -% b);
  assert ((a - b) % n = c % n);
  modulo_add n b (a-b) c;
  assert ((a - b + b) % n = (c + b) % n);
  assert (a % n = (c + b) % n);
  to_fe_idemp a;
  to_fe_add' c b

val add_comm: #n:big -> a:fe n -> b:fe n -> Lemma
  (a +% b = b +% a)
let add_comm #n _ _ = ()

val neg_zero: #n:big -> Lemma
  (neg (to_fe #n 0) = 0)
let neg_zero #n = ()

val add_sub_zero: #n:big -> a:fe n -> Lemma
  (a +% 0 = a /\ a -% 0 = a)
let add_sub_zero #n a = ()

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

val mod_as_multiple: #n:big -> a:fe n -> b:fe n -> v:fe n -> Lemma
  (requires (a - b = v * n))
  (ensures (a = b))
let mod_as_multiple #n a b v =
  to_fe_sub #n a b;
  to_fe_idemp #n b;
  assert ((a - b) % n = to_fe #n a -% b);

  cancel_mul_mod v n;
  assert (to_fe #n (v * n) = 0);

  assert (a -% b = 0);

  add_move_to_right a b 0;
  add_sub_zero b

val mul_zero: #n:big -> a:fe n -> Lemma
  (ensures (a *% 0 = 0 /\ 0 *% a = 0))
let mul_zero #n a = ()

val mul_one: #n:big -> a:fe n -> Lemma
  (ensures (a *% one = a /\ one *% a = a))
  [SMTPat (one *% a); SMTPat (a *% one)]
let mul_one #n a = ()

val mul_neg: #n:big -> a:fe n -> b:fe n -> Lemma
  (a *% (neg b) = neg (a *% b))
let mul_neg #n a b =
  if b = 0 || a = 0 then ()
  else
    calc (==) {
      a *% neg b;                         == { }
      (a * (n - b)) % n;                  == { distributivity_sub_right a n b }
      ((a * n) + (-(a * b))) % n;         == { modulo_distributivity (a * n) (-(a*b)) n }
      ((a * n) % n + (-(a * b)) % n) % n; == { multiple_modulo_lemma a n }
      ((-(a * b)) % n) % n;               == { lemma_mod_twice (-(a*b)) n }
      (-(a * b)) % n;                     == { to_fe_neg #n (a*b) }
      neg (to_fe #n (a*b));
    }

val mul_comm: #n:big -> a:fe n -> b:fe n -> Lemma
  (ensures (a *% b = b *% a))
  [SMTPat (a *% b)]
let mul_comm #n a b = ()

val mul_add_distr_r: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (a *% (b +% c) = a *% b +% a *% c)
let mul_add_distr_r #n a b c =
  to_fe_add' #n b c;
  to_fe_idemp a;
  to_fe_mul #n a (b+c);
  distributivity_add_right a b c;
  to_fe_add #n (a * b) (a * c);
  to_fe_mul' a b;
  to_fe_mul' a c

val mul_add_distr_l: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a +% b) *% c = a *% c +% b *% c)
let mul_add_distr_l #n a b c = mul_add_distr_r c a b

val mul_sub_distr_r: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (a *% (b -% c) = a *% b -% a *% c)
let mul_sub_distr_r #n a b c =
    calc (==) {
      a *% (b -% c);
    == { }
      a *% (b +% (neg c));
    == { mul_add_distr_r a b (neg c) }
      (a *% b) +% (a *% neg c);
    == { mul_neg a c }
      (a *% b) -% (a *% c);
    }

val mul_sub_distr_l: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a -% b) *% c = a *% c -% b *% c)
let mul_sub_distr_l #n a b c =
  mul_sub_distr_r c a b;
  mul_comm (a -% b) c

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
  == { lemma_mod_twice (a * b) n }
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
  mul_assoc a b (c *% d);
  mul_assoc b c d;
  mul_comm b c;
  mul_assoc c b d;
  mul_assoc a c (b *% d)

// Naive exp
val nexp: #n:big -> fe n -> e:nat -> Tot (fe n) (decreases e)
let rec nexp #n g e = match e with
  | 0 -> 1
  | 1 -> g
  | _ -> g *% nexp g (e-1)

val nexp_eq_arg1: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (requires (g1 = g2))
  (ensures (nexp g1 e = nexp g2 e))
let nexp_eq_arg1 #n _ _ _ = ()

val nexp_zero: #n:big -> e:pos -> Lemma
  (nexp #n 0 e = 0)
let rec nexp_zero #n e = match e with
  | 1 -> ()
  | _ -> nexp_zero #n (e-1)

val nexp_one1: #n:big -> g:fe n -> Lemma
  (ensures (nexp g one = g))
  [SMTPat (nexp g one)]
let nexp_one1 #n _ = ()

val nexp_one2: #n:big -> e:nat -> Lemma
  (ensures (nexp #n one e = one))
  [SMTPat (nexp #n one e)]
let rec nexp_one2 #n e = match e with
  | 0 -> ()
  | _ ->  nexp_one2 #n (e-1)

val nexp_mul1: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (nexp g e1 *% nexp g e2 = nexp g (e1 + e2))
let rec nexp_mul1 #n g e1 e2 = match e2 with
  | 0 -> assert(nexp g e2 = one)
  | 1 -> assert(nexp g e2 = g)
  | _ -> nexp_mul1 g e1 (e2-1)

val nexp_mul2: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (ensures (nexp (g1 *% g2) e = nexp g1 e *% nexp g2 e))
  (decreases e)
let rec nexp_mul2 #n g1 g2 e = match e with
  | 0 -> ()
  | 1 -> mul_one #n one
  | _ -> begin
    nexp_mul2 #n g1 g2 (e-1);
    mul4_assoc g1 g2 (nexp g1 (e-1)) (nexp g2 (e-1))
  end

val nexp_exp: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (ensures ((nexp (nexp g e1) e2) = (nexp g (e1 * e2))))
  (decreases e2)
let rec nexp_exp #n g e1 e2 = match e2 with
  | 0 -> if (nexp g e1) = 0 then () else nexp_zero #n (nexp g e1)
  | _ -> begin
    nexp_mul1 g e1 (e1 * e2 - e1);
    distributivity_sub_right e1 e2 1;
    nexp_exp #n g e1 (e2 - 1)
  end

// To subgroup
val to_fe_nexp1: #n:big -> k:big{n % k = 0 && n / k > 1 } -> g:fe n -> e:nat -> Lemma
  (to_fe #(n/k) (nexp g e) = nexp (to_fe #(n/k) g) e)
let rec to_fe_nexp1 #n k g e = match e with
  | 0 -> ()
  | 1 -> ()
  | _ -> begin
    let m = n / k in
    lemma_div_mod n k;
    assert (n = k * m);
    modulo_modulo_lemma (g * nexp g (e-1)) m k;
    assert (((g * nexp g (e-1)) % n) % m = (g * nexp g (e-1)) % m);
    assert ((g *% nexp g (e-1)) % m = (g * nexp g (e-1)) % m);
    assert (to_fe #m (g *% nexp g (e-1)) = to_fe #m (g * nexp g (e-1)));
    to_fe_nexp1 #n k g (e-1);
    to_fe_mul #m g (nexp g (e-1))
  end

// Define fexp' for composite n and for unit g.
val fexp: #n:big -> fe n -> e:nat -> Tot (fe n) (decreases e)
let rec fexp #n g e =
  if e = 1 then g
  else if e = 0 then 1
  else
     if e % 2 = 0
     then fexp (g *% g) (e / 2)
     else fexp (g *% g) ((e - 1) / 2) *% g

val fexp_eq_nexp: #n:big -> g:fe n -> e:nat -> Lemma
  (ensures (nexp g e = fexp g e)) (decreases e)
let rec fexp_eq_nexp #n g e = match e with
  | 0 -> ()
  | 1 -> ()
  | _ ->
    if e % 2 = 0
    then begin
      fexp_eq_nexp #n (g *% g) (e/2);
      nexp_exp #n g 2 (e/2)
    end
    else begin
      fexp_eq_nexp #n (g *% g) ((e-1)/2);
      nexp_exp g 2 ((e-1)/2)
    end

val fexp_two_is_sqr: #n:big -> g:fe n -> Lemma
  (fexp g 2 = sqr g)
let fexp_two_is_sqr #n _ = ()

val fexp_one1: #n:big -> g:fe n -> Lemma
  (ensures (fexp g one = g))
  [SMTPat (fexp g one)]
let fexp_one1 #n _ = ()

val fexp_one2: #n:big -> e:nat -> Lemma
  (ensures (fexp #n one e = one))
  [SMTPat (fexp #n one e)]
let fexp_one2 #n e = fexp_eq_nexp #n one e; nexp_one2 #n e

val fexp_zero1: #n:big -> e:pos -> Lemma
  (fexp #n 0 e = 0)
let fexp_zero1 #n e = fexp_eq_nexp #n 0 e; nexp_zero #n e

val fexp_zero2: #n:big -> g:fe n{g <> 0} -> Lemma
  (fexp #n g 0 = 1)
let fexp_zero2 #n _ = ()

val fexp_mul1: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (fexp g e1 *% fexp g e2 = fexp g (e1 + e2))
let fexp_mul1 #n g e1 e2 =
  fexp_eq_nexp g e1;
  fexp_eq_nexp g e2;
  fexp_eq_nexp g (e1+e2);
  nexp_mul1 g e1 e2

val fexp_mul2: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (fexp (g1 *% g2) e = fexp g1 e *% fexp g2 e)
let fexp_mul2 #n g1 g2 e =
  fexp_eq_nexp (g1 *% g2) e;
  fexp_eq_nexp g1 e;
  fexp_eq_nexp g2 e;
  nexp_mul2 g1 g2 e

val fexp_exp: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (fexp #n (fexp #n g e1) e2 = fexp #n g (e1 * e2))
let fexp_exp #n g e1 e2 =
  fexp_eq_nexp g e1;
  fexp_eq_nexp (nexp g e1) e2;
  fexp_eq_nexp g (e1 * e2);
  nexp_exp g e1 e2

// Probably needs slightly more lemma to prove then there are here
val flt: #p:prm -> a:fe p{a>0} -> Lemma
  (fexp a (p-1) = 1)
let flt #p _ = admit()

(* Inverses *)

// euler's totient
val phi: big -> pos
let phi n = if isprm n then n-1 else admit()

val isunit: #n:big -> a:fe n -> Type0
let isunit #n a = exists b. a *% b = 1

val isunit_nonzero: #n:big -> g:fe n{isunit g} -> Lemma (g <> 0)
let isunit_nonzero #n g =
  assert (g = 0 ==> (forall x. g * x = 0));
  assert (g = 0 ==> (forall x. (g * x) % n = 0))

val one_isunit: n:big -> Lemma (isunit #n 1)
let one_isunit _ = ()

// Based on euler's theorem
val finv0: #n:big -> a:fe n ->
  Tot (b:fe n{isunit a <==> b *% a = one})
let finv0 #n a =
  admit();
  let (g,u,_) = ex_eucl a n in
  if g = 1 then u else 0

val finv: #n:big -> a:fe n{isunit a} -> b:fe n{b *% a = one}
let finv #n a = finv0 a

val finv_unique: #n:big -> a:fe n -> b:fe n{a *% b = one} -> Lemma
  (isunit a /\ b = finv a)
let finv_unique #n a b =
  let z = finv a in
  calc (==) {
    z; =={} z *% one; =={} z *% (a *% b); =={}
            (z *% a) *% b; =={} one *% b; =={} b;
  }

val finv_mul: #n:big -> a:fe n -> b:fe n{isunit b} -> c:fe n -> Lemma
  (requires (a = b *% c))
  (ensures (a *% finv b = c))
let finv_mul #n a b c =
  assert (a *% finv b = (b *% c) *% finv b);
  mul_comm (b *% c) (finv b);
  mul_assoc (finv b) b c

val isunit_prod: #n:big -> a:fe n{isunit a} -> b:fe n{isunit b} -> Lemma
  (ensures (isunit (a *% b) /\ finv (a *% b) = finv a *% finv b))
let isunit_prod #n a b =
  mul4_assoc a b (finv a) (finv b);
  assert((a *% b) *% (finv a *% finv b) = one);
  finv_unique (a *% b) (finv a *% finv b)

val inv_as_gcd1: #n:big -> a:fe n{a>0} -> Lemma
  (requires (gcd a n = 1))
  (ensures (isunit a))
let inv_as_gcd1 #n a =
  let (g,u,v) = ex_eucl a n in
  assert (gcd a n = g);

  assert (((u*a)%n = (1 + (-v)*n)%n));
  modulo_distributivity 1 ((-v)*n) n;
  assert ((u*a)%n = (1%n + ((-v)*n)%n)%n);
  multiple_modulo_lemma (-v) n;
  assert ((u*a)%n = (1%n)%n);
  lemma_mod_twice 1 n;
  one_mod_n n;
  assert ((u*a)%n = 1);
  modulo_mul_distributivity u a n;
  assert (((to_fe #n u)*(a%n))%n = 1);
  modulo_lemma a n;
  assert ((to_fe #n u *% a) = 1);
  finv_unique #n (to_fe u) a

val inv_as_gcd2: #n:big -> a:fe n{a>0} -> Lemma
  (requires (isunit a))
  (ensures (gcd a n = 1))
let inv_as_gcd2 #n a =
  let u:fe n = finv a in

  mod_prop n (u*a) 1;
  assert ((u * a) + (-((u*a)/n)*n) = 1);
  neg_mul_left ((u*a)/n) n;
  ex_eucl_lemma3 a n u (-(u*a)/n)

val inv_as_gcd: #n:big -> a:fe n{a>0} -> Lemma
  (isunit a <==> gcd a n = 1)
let inv_as_gcd #n a =
  move_requires inv_as_gcd1 a;
  move_requires inv_as_gcd2 a

// Could be some naive algorithm, not used in the real code.
val mult_order:
     #n:big
  -> g:fe n{isunit g}
  -> r:pos{ fexp g r = one /\
            (forall (x:pos{x<r}). fexp g x <> one) /\
            (r >= 1)
            }
let mult_order #n g = admit()

val g_pow_order_reduc: #n:big -> g:fe n{isunit g /\ g > 0} -> x:pos -> Lemma
  (ensures (fexp g x = fexp g (x % mult_order g)))
  (decreases x)
let rec g_pow_order_reduc #n g x =
  let r = mult_order g in
  if x < r
  then modulo_lemma x r
  else begin
    lemma_div_mod x r;
    assert(x = r * (x / r) + x % r);
    fexp_mul1 g (r * (x/r)) (x%r);
    fexp_exp g r (x/r);
    assert(fexp g r = one);
    fexp_one2 #n (x/r)
  end

val g_pow_inverse: #n:big -> g:fe n{isunit g} -> x:pos -> Lemma
  (let r = mult_order g in
   isunit (fexp g x) /\
   finv (fexp g x) = fexp g (r - (x % r)))
let g_pow_inverse #n g x =
  isunit_nonzero #n g;
  let r = mult_order g in
  let x' = x % r in
  modulo_range_lemma x r;
  let inv_e = r - x' in
  assert(inv_e >= 0 && inv_e <= r);
  assert(fexp g r = one);
  g_pow_order_reduc g x;
  fexp_mul1 g x' inv_e;
  assert(fexp g x' *% fexp g (r - x') = one);
  assert(fexp g x *% fexp g (r - x') = one);
  finv_unique (fexp g x) (fexp g (r - x'))

val g_pow_isunit: #n:big -> g:fe n -> x:pos -> Lemma
  (requires (isunit g))
  (ensures (isunit (fexp g x)))
let g_pow_isunit #n g x = g_pow_inverse g x
