module Lib.Math.Algebra

open FStar.Calc
open FStar.Constructive
open FStar.Classical
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
open FStar.Squash

module L = FStar.List.Tot


(* Divisibisity *)

type big = x:int{x > 1}

val one: pos
let one = 1

val zero_mod_n: n:pos -> Lemma (0 % n = 0)
let zero_mod_n _ = ()

val one_mod_n: n:big -> Lemma (1 % n = 1)
let one_mod_n _ = ()

let divides (a:pos) (b:int):bool = b % a = 0

val divides_sum: a:pos -> b:int -> c:int -> Lemma
  ((divides a b /\ divides a c) ==> divides a (b+c))
let divides_sum a b c = modulo_distributivity c b a

val divides_mult1: a:pos -> b:int -> n:nat -> Lemma
  (divides a b ==> divides a (n*b))
let rec divides_mult1 a b n = match n with
  | 0 -> ()
  | _ -> divides_mult1 a b (n-1); modulo_distributivity ((n-1)*b) b a

val divides_mult2: a:pos -> b:int -> n:int{n<=0} -> Lemma
  (requires True)
  (ensures (divides a b ==> divides a (n*b)))
  (decreases (-n))
let rec divides_mult2 a b n = match n with
  | 0 -> ()
  | _ -> divides_mult2 a b (n+1); modulo_distributivity (n*b) b a

val divides_mult: a:pos -> b:int -> n:int -> Lemma
  (divides a b ==> divides a (n*b))
let divides_mult a b n =
  if n >= 0 then divides_mult1 a b n else divides_mult2 a b n

val divides_neg: a:pos -> b:int -> Lemma
  (divides a b ==> divides a (-b))
let divides_neg a b = divides_mult a b (-1)

val divides_sum_rev: c:pos -> a:int -> b:int -> Lemma
  ((divides c (a+b) /\ divides c b) ==> divides c a)
let divides_sum_rev c a b =
  divides_neg c b;
  divides_sum c (a+b) (-b)

val divides_prod: a:pos -> b:pos -> c:int -> Lemma
  (requires divides (a*b) c)
  (ensures (divides a c /\ divides b c))
let divides_prod a b c =
  mod_mult_exact c a b;
  mod_mult_exact c b a

val isprm: p:nat -> Type0
let isprm p = p >= 3 /\ p % 2 = 1 /\ (forall (x:nat{x>1&&x<p}). ~(divides x p))

type prm = p:big{isprm p}

val iscomp: n:big -> Type0
let iscomp n = exists (p:prm) (q:prm{q<>p}). n = p * q

type comp = n:big{iscomp n}

// In some cases F* can't decide the existential description
val mkcomp: p:prm -> q:prm{p <> q} -> comp
let mkcomp p q = p * q

// These two functions are useful for working with pair of factors.
val exists_elim_pair (goal:Type) (#a:Type) (#b:Type) (#p:(a -> b -> Type))
  (_:squash (exists (x:a) (y:b). p x y))
  (_:(x:a -> y:b{p x y} -> GTot (squash goal))) :Lemma goal
let exists_elim_pair goal #a #b #p have f =
  let joined1: squash (x:a & (exists (y:b). p x y)) = join_squash have in
  bind_squash #_ #goal joined1 (fun (| x, pf1 |) ->
    let joined2: squash (y:b & p x y) = join_squash (return_squash pf1) in
    bind_squash joined2 (fun (|y, pf2|) -> return_squash pf2; f x y))

// These two functions are useful for working with pair of factors.
val exists_elim_pair_dep (goal:Type) (#a:Type) (#b:a -> Type) (#p:(x:a -> b x -> Type))
  (_:squash (exists (x:a) (y:b x). p x y))
  (_:(x:a -> y:b x{p x y} -> GTot (squash goal))) :Lemma goal
let exists_elim_pair_dep goal #a #b #p have f =
  let joined1: squash (x:a & (exists (y:b x). p x y)) = join_squash have in
  bind_squash #_ #goal joined1 (fun (| x, pf1 |) ->
    let joined2: squash (y:b x & p x y) = join_squash (return_squash pf1) in
    bind_squash joined2 (fun (|y, pf2|) -> return_squash pf2; f x y))

val ex_pair: #a:Type -> #b:Type -> p:(a -> b -> bool) -> Lemma
  (requires (exists x y. p x y))
  (ensures (exists xy. p (fst xy) (snd xy)))
let ex_pair #a #b p =
  let ex2: squash (exists (x:a) (y:b). p x y) = () in
  let goal = exists xy. p (fst xy) (snd xy) in
  exists_elim_pair
    goal
    ex2
    (fun x y -> let xy = Mktuple2 x y in assert(p (fst xy) (snd xy)))

val ex_pair_inv: #a:Type -> #b:Type -> p:(a -> b -> bool) -> Lemma
  (requires (exists xy. p (fst xy) (snd xy)))
  (ensures (exists x y. p x y))
let ex_pair_inv #a #b p = ()

val ex_pair_dep: #a:Type -> #b:(a -> Type) -> p:(x:a -> b x -> bool) -> Lemma
  (requires (exists x y. p x y))
  (ensures (exists xy. let Mkdtuple2 x y = xy in p x y))
let ex_pair_dep #a #b p =
  let ex2: squash (exists (x:a) (y:b x). p x y) = () in
  let goal = exists xy. let Mkdtuple2 x y = xy in p x y in
  exists_elim_pair_dep
    goal
    ex2
    (fun (x:a) (y:b x{p x y}) -> let xy = Mkdtuple2 x y in assert (let Mkdtuple2 x y = xy in p x y))

val ex_pair_dep_inv: #a:Type -> #b:(a -> Type) -> p:(x:a -> b x -> bool) -> Lemma
  (requires (exists xy. let Mkdtuple2 x y = xy in p x y))
  (ensures (exists x y. p x y))
let ex_pair_dep_inv #a #b p = ()

val exists_intro_2_dep (#a:Type) (#b:a -> Type) (p:(x:a -> b x -> Type)) (w1:a) (w2:b w1)
  :Lemma (requires (p w1 w2)) (ensures (exists (x:a) (y:b x). p x y))
let exists_intro_2_dep #a #b p w1 w2 =
  exists_intro (fun xy -> let Mkdtuple2 x y = xy in p x y) (Mkdtuple2 w1 w2)

// Prove statements about composite numbers without being given
// explicit factorisation.
val comp_elim:
     n:comp
  -> #goal:Type0
  -> f:(p:prm -> q:prm{p <> q /\ p*q = n} -> squash goal)
  -> Lemma goal
let comp_elim n #goal f =
  exists_elim goal #(x:(tuple2 prm prm))
      #(fun x -> fst x <> snd x /\ fst x * snd x = n)
      (ex_pair #prm #prm (fun p q -> p <> q && p * q = n))
      (fun x -> f (fst x) (snd x))

val modulo_mul_distributivity: a:int -> b:int -> n:pos ->
    Lemma ((a * b) % n = ((a % n) * (b % n)) % n)
let rec modulo_mul_distributivity a b n =
  lemma_mod_mul_distr_l a b n;
  lemma_mod_mul_distr_r (a % n) b n

val divides_multiple: a:pos -> b:pos{divides a b} -> k:pos -> Lemma
  (divides a (k*b))
let divides_multiple a b k = modulo_mul_distributivity k b a

let is_common_divisor (a:nat) (b:nat) (g:pos) = divides g a && divides g b

// Notion of gcd is extended here to cover the euclidian algorithm
// logic -- we allow a to be zero. Most of the lemmas apply to the
// case when both arguments are positive, but some lemmas need first
// one to be zero.
type is_gcd (a:nat) (b:pos) (g:pos) =
       is_common_divisor a b g /\
       (forall (x:pos{x>g}). ~(is_common_divisor a b x))

val gcd_symm: a:pos -> b:pos -> g:pos -> Lemma
  (is_gcd a b g ==> is_gcd b a g)
let gcd_symm a b g = ()

val gcd_upper_bound: a:pos -> b:pos -> g:pos{is_gcd a b g} -> Lemma
  (g <= a /\ g <= b /\ g <= min a b)
let gcd_upper_bound a b g = ()

#reset-options "--z3rlimit 100"

val find_gcd_naive:
     a:pos
  -> b:pos
  -> g_cur:pos{g_cur <= min a b}
  -> g_last:pos{g_last < g_cur /\ is_common_divisor a b g_last /\
                (forall (g':pos{g'>g_last /\ g' < g_cur}). ~(is_common_divisor a b g'))}
  -> Tot (g:pos{is_gcd a b g})
         (decreases (min a b - g_cur))
let rec find_gcd_naive a b g_cur g_last =
  let m = min a b in
  if g_cur = m then
    (if is_common_divisor a b g_cur then g_cur else g_last)
  else begin
    find_gcd_naive a b (g_cur + 1) (if is_common_divisor a b g_cur then g_cur else g_last)
  end

#reset-options

val gcd_exists: a:pos -> b:pos -> Lemma (exists (g:pos). is_gcd a b g)
let gcd_exists a b =
  assert (a > 0 && b > 0);
  assert (is_common_divisor a b 1);
  if min a b = 1
    then assert (is_gcd a b 1)
    else (let g = find_gcd_naive a b 2 1 in assert (is_gcd a b g))

val gcd_unique: a:pos -> b:pos -> g1:pos{is_gcd a b g1} -> g2:pos{is_gcd a b g2} -> Lemma
  (g1 == g2)
let gcd_unique a b g1 g2 = ()

val gcd_intro_forall: a:pos -> b:pos -> g:pos{is_gcd a b g} -> p:(pos -> Type0){p g} -> Lemma
  (forall g'. is_gcd a b g' ==> p g')
let gcd_intro_forall a b g p =
  assert (forall g'. is_gcd a b g' ==> g = g');
  assert (forall g'. is_gcd a b g' ==> p g')

val gcd_exists_elim: a:pos -> b:pos -> g:pos -> Lemma
  (requires (exists (g':pos{is_gcd a b g'}). g' = g))
  (ensures (is_gcd a b g))
let gcd_exists_elim a b g = ()

val gcd_forall_to_exists: a:pos -> b:pos -> p:(g:pos{is_gcd a b g} -> Type0) -> Lemma
  (requires (forall (g:pos{is_gcd a b g}). p g))
  (ensures (exists (g:pos{is_gcd a b g}). p g))
let gcd_forall_to_exists a b p =
  gcd_exists a b;
  assert (exists g. is_gcd a b g);
  assert (exists g. is_gcd a b g ==> p g)

val gcd_forall_elim: a:pos -> b:pos -> g:pos -> Lemma
  (requires (forall (g':pos{is_gcd a b g'}). g' = g))
  (ensures (is_gcd a b g))
let gcd_forall_elim a b g = gcd_forall_to_exists a b (fun g' -> g' = g)

val gcd_divides: a:pos -> b:pos -> Lemma
  (requires divides a b)
  (ensures is_gcd a b a)
let gcd_divides a b = ()

val gcd_prop_add_arg: a:nat -> b:pos -> g:pos{is_gcd a b g} -> Lemma
  (is_gcd (a+b) b g)
let gcd_prop_add_arg a b g =
  exists_elim (is_gcd (a+b) b g) #pos #(fun g' -> is_gcd (a+b) b g') (gcd_exists (a+b) b)
    (fun g' -> begin
       if g' > g then begin
         divides_neg g' b;
         divides_sum g' (a+b) (-b);
         assert (divides g' a);
         assert (is_gcd a b g');
         assert (False);
         assert (is_gcd (a+b) b g)
       end else begin
         divides_sum g a b;
         assert (is_gcd (a+b) b g)
       end
     end)

val gcd_prop_sub_arg: a:nat -> b:pos -> g:pos{is_gcd a b g} -> Lemma
  (requires (a-b > 0))
  (ensures (is_gcd (a-b) b g))
let gcd_prop_sub_arg a b g =
  exists_elim (is_gcd (a-b) b g) #pos #(fun g' -> is_gcd (a-b) b g') (gcd_exists (a-b) b)
    (fun g' -> begin
       if g' > g then begin
         divides_neg g' b;
         divides_sum g' (a-b) b;
         assert (divides g' a);
         assert (is_gcd a b g');
         assert (False);
         assert (is_gcd (a-b) b g)
       end else begin
         divides_neg g b;
         divides_sum g a (-b);
         assert (is_gcd (a-b) b g)
       end
     end)


val gcd_prop_multiple1: a:nat -> b:pos -> g:pos -> m:nat -> Lemma
  (requires (is_gcd a b g /\ a + m*b >= 0))
  (ensures (is_gcd (a + m*b) b g))
let rec gcd_prop_multiple1 a b g m = match m with
  | 0 -> ()
  | 1 -> gcd_prop_add_arg a b g
  | _ -> gcd_prop_multiple1 a b g (m-1); gcd_prop_add_arg (a+(m-1)*b) b g

val gcd_prop_multiple2: a:nat -> b:pos -> g:pos -> m:int{m <= 0} -> Lemma
  (requires (is_gcd a b g /\ a + m*b > 0))
  (ensures (is_gcd (a + m*b) b g))
  (decreases (-m))
let rec gcd_prop_multiple2 a b g m = match m with
  | 0 -> ()
  | x -> if x = -1
         then gcd_prop_sub_arg a b g
         else begin
           gcd_prop_multiple2 a b g (m+1);
           gcd_prop_sub_arg (a+(m+1)*b) b g
         end

val gcd_prop_multiple: a:nat -> b:pos -> g:pos -> m:int -> Lemma
  (requires (is_gcd a b g /\ a + m*b > 0))
  (ensures (is_gcd (a + m*b) b g))
let gcd_prop_multiple a b g m =
  if m >= 0 then gcd_prop_multiple1 a b g m else gcd_prop_multiple2 a b g m

val ex_eucl_raw:
     a:nat
  -> b:pos
  -> r:tuple3 pos int int{ let (g,u,v) = r in a * u + b * v = g }
let rec ex_eucl_raw a b =
  if a = 0 then (b, 0, 1) else begin
    modulo_range_lemma b a;
    let (g,s,t) = ex_eucl_raw (b % a) a in
    distributivity_sub_left t ((b/a)*s) a;
    lemma_div_mod b a;
    (g, t - (b / a) * s, s)
  end

val gcd_eucl_step:
     a:pos
  -> b:pos
  -> g:pos
  -> Lemma (requires is_gcd (b % a) a g) (ensures (is_gcd a b g))
let rec gcd_eucl_step a b g =
  assert (is_gcd (b % a) a g);
  lemma_div_mod b a;
  assert (b % a = b - a * (b / a));
  assert (b - a * (b / a) = b + (- (b/a)) * a);
  assert (b + (- (b/a)) * a >= 0);
  gcd_prop_multiple (b - a * (b/a)) a g (b/a);
  assert (is_gcd b a g);
  gcd_symm b a g

val ex_eucl_raw_is_gcd:
     a:nat
  -> b:pos
  -> Lemma (let (g,_,_) = ex_eucl_raw a b in is_gcd a b g)
let rec ex_eucl_raw_is_gcd a b =
  if a = 0 then () else begin
    modulo_range_lemma b a;
    let (g,_,_) = ex_eucl_raw (b % a) a in
    ex_eucl_raw_is_gcd (b % a) a;
    gcd_eucl_step a b g
  end

val ex_eucl:
     a:nat
  -> b:pos
  -> r:tuple3 pos int int{ let (g,u,v) = r in is_gcd a b g /\ a * u + b * v = g }
let rec ex_eucl a b = ex_eucl_raw_is_gcd a b; ex_eucl_raw a b

val gcd: a:pos -> b:pos -> g:pos{is_gcd a b g}
let gcd a b = Mktuple3?._1 (ex_eucl a b)

val gcd_standalone: a:nat -> b:pos -> g:pos{is_gcd a b g}
let rec gcd_standalone a b =
  if a = 0
  then b
  else
    (modulo_range_lemma b a;
     let g = gcd_standalone (b % a) a in
     gcd_eucl_step a b g;
     g)

val gcd_prop_subdiv: a:pos -> b:pos -> g:pos{is_gcd a b g} -> d:pos -> Lemma
  (divides d a /\ divides d b ==> divides d g)
let gcd_prop_subdiv a b g d =
  let (g',u,v) = ex_eucl a b in
  assert (g'= g);
  assert (u*a + v*b = g);

  let l (): Lemma (requires (divides d a /\ divides d b))
                       (ensures (divides d g)) =
          divides_mult d a u;
          divides_mult d b v;
          divides_sum d (a * u) (b * v)
          in

  move_requires l ()

val gcd_mod_nonzero: a:pos -> b:pos -> g:pos -> Lemma
  (requires (a <> b /\ is_gcd a b g /\ g < a))
  (ensures ~(divides a b))
let gcd_mod_nonzero a b g = assert (divides a b ==> is_gcd a b a)

val gcd_one_different: a:pos -> b:pos -> Lemma
  (requires (is_gcd a b 1 /\ a > 1))
  (ensures a <> b)
let gcd_one_different a b = assert (a = b ==> is_gcd a b a)

// n = a = 1 is the only input combination that gives a % n = 0
val gcd_mod_reduce: n:pos -> a:pos -> Lemma
  (requires (is_gcd a n 1))
  (ensures ((a % n) = 0 \/ is_gcd (a % n) n 1))
let gcd_mod_reduce n a =
  if a % n <> 0 then
  exists_elim (is_gcd (a % n) n 1) #pos #(fun g -> is_gcd (a % n) n g)
    (gcd_exists (a % n) n)
    (fun g -> if g > 1 then begin
      assert (divides g (a % n));
      assert (divides g n);
      lemma_div_mod a n;
      divides_mult g n (a/n);
      divides_neg g (n * (a/n));
      divides_sum_rev g a (-(n*(a/n)));
      assert (divides g a);
      assert (is_gcd a n g);
      assert (False);
      assert (is_gcd (a % n) n 1)
     end)

val gcd_mod_reduce_big: n:big -> a:pos -> Lemma
  (requires (is_gcd a n 1))
  (ensures (is_gcd (a % n) n 1))
let gcd_mod_reduce_big n a =
  gcd_mod_reduce n a;
  gcd_one_different n a;
  assert (a <> n);
  gcd_mod_nonzero n a 1

val gcd_with_prime: p:prm -> a:pos -> Lemma
  (requires (~(divides p a)))
  (ensures (is_gcd a p 1))
let gcd_with_prime p a =
  assert (a < p ==> is_gcd a p 1);
  assert (is_gcd (a % p) p 1);
  lemma_div_mod a p;
  assert (a = a % p + (a / p) * p);
  gcd_prop_multiple (a % p) p 1 (a / p);
  assert (is_gcd a p 1)

#reset-options "--z3rlimit 100"

val ex_eucl_lemma1: a:pos -> b:pos -> j:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = j))
  (ensures (let g = gcd a b in j = g * ((a/g)*u+(b/g)*v)))
let ex_eucl_lemma1 a b j u v =
  // a * u + b * v = g * (a' * u + b' * v)

  let goal = (let g = gcd a b in j = gcd a b * ((a/g)*u+(b/g)*v)) in
  let lemma (g:pos{is_gcd a b g}): Lemma goal = begin
    lemma_div_mod a g;
    lemma_div_mod b g;
    assert (a = g * (a / g) /\ b = g * (b / g));
    assert (g * (a / g) * u + g * (b / g) * v = j);
    distributivity_add_right g ((a / g) * u) ((b / g) * v);
    assert (g * ((a / g) * u + (b / g) * v) = j);
    assert (j = gcd a b * ((a / g) * u + (b / g) * v))
  end in

  exists_elim goal #pos #(fun g -> is_gcd a b g) (gcd_exists a b) (fun g -> lemma g)

val ex_eucl_lemma2: a:pos -> b:pos -> j:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = j /\ divides j a /\ divides j b))
  (ensures (gcd a b = j))
let ex_eucl_lemma2 a b j u v =
  ex_eucl_lemma1 a b j u v;
  let g = gcd a b in
  let t = (a/g)*u + (b/g)*v in
  assert (j = g * t);
  assert (is_gcd a b g);
  assert (is_common_divisor a b j);
  assert (t > 1 ==> False); // then j > g, but g is gcd
  assert (t > 0); // because g, j are positive
  assert (t <> 0); // because j > 0
  assert (t = 1)

#reset-options

val ex_eucl_lemma3: a:pos -> b:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = 1))
  (ensures (gcd a b = 1))
let ex_eucl_lemma3 a b u v = ex_eucl_lemma2 a b 1 u v

type is_common_multiple (a:pos) (b:pos) (l:pos) =
  divides a l /\ divides b l

val lcm: pos -> pos -> pos
let lcm a b = (a / gcd_standalone a b) * b

val multiplication_order_lemma_strict: a:int -> b:int -> p:pos ->
    Lemma (a < b <==> a * p < b * p)
let multiplication_order_lemma_strict a b p = ()

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
  (a / b <= a)
let division_post_size a b = division_definition_lemma_1 a b a

val division_post_size2: a:pos -> b:pos{b>1} -> Lemma
  (a / b < a)
let division_post_size2 a b = division_definition_lemma_1 a b a

val lcm_less_mul: a:pos -> b:pos -> Lemma
  (lcm a b <= a * b)
let lcm_less_mul a b =
  let g:pos = gcd a b in
  assert (lcm a b = (a / g) * b);
  division_mul_after a b g;
  assert (lcm a b = (a * b) / g);
  division_post_size (a * b) g

// https://math.stackexchange.com/questions/1319766/is-it-true-that-pq-p-1q-1-1-iff-pq-operatornamelcmp-1-q-1-1
val gcd_pq_lcm_lemma: p:pos{p>1} -> q:pos{q>1} -> Lemma
  (gcd (p * q) ((p - 1) * (q - 1)) = 1 <==>
   gcd (p * q) (lcm (p-1) (q-1)) = 1)
let gcd_pq_lcm_lemma _ _ = admit()

val gcd_to_factor: n:pos -> m:pos -> a:pos -> g:pos -> Lemma
  (requires (is_gcd a (n*m) g))
  (ensures (forall g'. (is_gcd a n g' ==> g' <= g)))
let gcd_to_factor n m a g =
  let k = n * m in

  exists_elim (forall g'. (is_gcd a n g' ==> g' <= g))
    #pos #(fun g' -> is_gcd a n g') (gcd_exists a n)
    (fun g' -> begin
      if g' > g then begin
        assert (divides g' a /\ divides g' n);
        divides_mult1 g' n m;
        assert (divides g' a /\ divides g' k);
        assert (is_gcd a k g');
        assert (False);
        assert (g' <= g)
      end;
      gcd_intro_forall a n g' (fun g'' -> g'' <= g)
    end)

val gcd_to_factor_one: n:pos -> m:pos -> a:pos -> Lemma
  (requires (is_gcd a (n*m) 1))
  (ensures (is_gcd a n 1))
let gcd_to_factor_one n m a =
  gcd_to_factor n m a 1;
  assert (forall g'. (is_gcd a n g' ==> g' = 1));
  gcd_forall_elim a n 1


(* Algebra *)

val field_el: #n:big -> a:int -> bool
let field_el #n a = a >= 0 && a < n

type fe n = x:int{field_el #n x}

val to_fe: #n:big -> a:int -> r:fe n
let to_fe #n a = lemma_mod_lt a n; a % n

val to_fe_bigger_and_back: #n:big -> m:big{m>=n} -> a:fe n -> Lemma
  (to_fe #n (to_fe #m a) = a)
let to_fe_bigger_and_back #n m a = ()

val to_fe_idemp_raw: n:big -> a:nat -> Lemma
  (a < n ==> to_fe #n a = a)
let to_fe_idemp_raw n a = ()

val to_fe_idemp: #n:big -> a:fe n -> Lemma
  (to_fe #n a = a)
let to_fe_idemp #n a = ()

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

#reset-options "--z3rlimit 100"

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

#reset-options

val to_fe_add: #n:big -> a:int -> b:int -> Lemma
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

val to_fe_mul: #n:big -> a:int -> b:int -> Lemma
  (to_fe #n (a * b) = to_fe a *% to_fe b)
let to_fe_mul #n a b = modulo_mul_distributivity a b n

val to_fe_mul': #n:big -> a:fe n -> b:fe n -> Lemma
  (to_fe #n (a * b) = a *% b)
let to_fe_mul' #n a b = to_fe_mul #n a b

#set-options "--z3rlimit 100"

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

#reset-options

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

val add3_modulo_out_l: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a +% b) +% c = ((a + b) + c) % n)
let add3_modulo_out_l #n a b c =
  calc (==) {
   (a +% b) +% c;
  == { }
   ( (a + b) % n ) +% c;
  == { }
   ( ((a + b) % n) + c ) % n;
  == { modulo_distributivity ((a + b) % n) c n }
   ( (((a + b) % n) % n) + (c % n) ) % n;
  == { lemma_mod_twice (a + b) n }
   ( ((a + b) % n) + (c % n)) % n;
  == { modulo_distributivity (a + b) c n }
   ( (a + b) + c ) % n;
  }

val add3_modulo_out_r: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (a +% (b +% c) = (a + (b + c)) % n)
let add3_modulo_out_r #n a b c =
  calc (==) {
    a +% (b +% c);
   == { add3_modulo_out_l #n b c a }
    ((b + c) + a) % n;
   == { }
    (a + (b + c)) % n;
  }

val add_assoc: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (ensures ((a +% b) +% c = a +% (b +% c)))
  [SMTPat ((a +% b) +% c); SMTPat (a +% (b +% c))]
let add_assoc #n a b c =
  calc (==) {
    (a +% b) +% c;
  == { add3_modulo_out_l a b c }
    ((a + b) + c) % n;
  == { }
    (a + (b + c)) % n;
  == { add3_modulo_out_r a b c }
    (a +% (b +% c));
  }


val neg_zero: #n:big -> Lemma
  (neg (to_fe #n 0) = 0)
let neg_zero #n = ()

val add_sub_zero: #n:big -> a:fe n -> Lemma
  (a +% 0 = a /\ a -% 0 = a)
let add_sub_zero #n a = ()

val mod_prop: n:pos -> a:int -> b:int -> Lemma
  (requires (a % n = b))
  (ensures (a - b = (a / n) * n))
let mod_prop n a b =
  lemma_div_mod a n;
  assert(a % n = a - n * (a / n));
  assert(b = a - n * (a / n));
  assert(a - b = (a / n) * n)

val mod_prop_inv: n:big -> a:int -> b:int -> k:int -> Lemma
  (requires (a = b + k * n))
  (ensures (a % n = b % n))
let mod_prop_inv n a b k =
  assert (a % n = (b + k * n) % n);
  modulo_distributivity b (k * n) n;
  assert (a % n = (b % n + (k * n) % n) % n);
  multiple_modulo_lemma k n;
  assert (a % n = (b % n) % n);
  modulo_modulo_lemma b n 1;
  assert (a % n = b % n)

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

(*** Exponents ***)

// Naive exp
val nexp: nat -> e:nat -> Tot nat (decreases e)
let rec nexp g e = match e with
  | 0 -> 1
  | 1 -> g
  | _ -> g * nexp g (e-1)

val nexp_bigger_than_base: g:nat -> e:nat -> Lemma (g > 0 /\ e > 0 ==> nexp g e >= g)
  [SMTPat (nexp g e)]
let nexp_bigger_than_base g0 e0 =
  let rec go g e: Lemma (requires (g>0/\e>0)) (ensures (nexp g e >= g)) =
      if e = 1 then () else go g (e-1) in
  move_requires (go g0) e0

val nexp_eq_arg1: g1:nat -> g2:nat -> e:nat -> Lemma
  (requires (g1 = g2))
  (ensures (nexp g1 e = nexp g2 e))
let nexp_eq_arg1 _ _ _ = ()

val nexp_zero: e:pos -> Lemma
  (nexp 0 e = 0)
let rec nexp_zero e = match e with
  | 1 -> ()
  | _ -> nexp_zero (e-1)

val nexp_one1: g:pos -> Lemma
  (ensures (nexp g one = g))
  [SMTPat (nexp g one)]
let nexp_one1 _ = ()

val nexp_one2: e:nat -> Lemma
  (ensures (nexp one e = one))
  [SMTPat (nexp one e)]
let rec nexp_one2 e = match e with
  | 0 -> ()
  | _ ->  nexp_one2 (e-1)

#reset-options

val nexp_mul1: g:nat -> e1:nat -> e2:nat -> Lemma
  (nexp g e1 * nexp g e2 = nexp g (e1 + e2))
let rec nexp_mul1 g e1 e2 = match e2 with
  | 0 -> assert(nexp g e2 = one)
  | 1 -> assert(nexp g e2 = g)
  | _ -> nexp_mul1 g e1 (e2-1);
         swap_mul (nexp g (e2 - 1)) g;
         swap_mul (nexp g (e1 + e2 - 1)) g;
         paren_mul_right (nexp g e1) (nexp g (e2-1)) g

val mul4_assoc_nomod: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  ((a * b) * (c * d) = (a * c) * (b * d))
let mul4_assoc_nomod a b c d =
  let mul_assoc_nomod x y z = paren_mul_right x y z; paren_mul_left x y z in
  mul_assoc_nomod a b (c * d);
  mul_assoc_nomod b c d;
  swap_mul b c;
  mul_assoc_nomod c b d;
  mul_assoc_nomod a c (b * d)

val nexp_mul2: g1:nat -> g2:nat -> e:nat -> Lemma
  (ensures (nexp (g1 * g2) e = nexp g1 e * nexp g2 e))
  (decreases e)
let rec nexp_mul2 g1 g2 e = match e with
  | 0 -> ()
  | 1 -> ()
  | _ ->
    nexp_mul2 g1 g2 (e-1);
    mul4_assoc_nomod g1 g2 (nexp g1 (e-1)) (nexp g2 (e-1))

val nexp_exp: g:nat -> e1:nat -> e2:nat -> Lemma
  (ensures ((nexp (nexp g e1) e2) = (nexp g (e1 * e2))))
  (decreases e2)
let rec nexp_exp g e1 e2 = match e2 with
  | 0 -> if (nexp g e1) = 0 then () else nexp_zero (nexp g e1)
  | _ -> begin
    nexp_mul1 g e1 (e1 * e2 - e1);
    distributivity_sub_right e1 e2 1;
    nexp_exp g e1 (e2 - 1)
  end

val nexp_greater_than_power: g:pos{g>1} -> e:nat -> Lemma
  (nexp g e > e)
let rec nexp_greater_than_power g e =
  if e = 0 then () else nexp_greater_than_power g (e-1)

val exp: nat -> e:nat -> Tot nat (decreases e)
let rec exp g e =
  if e = 0 then 1
  else if e = 0 then g
  else
     if e % 2 = 0
     then exp (g * g) (e / 2)
     else exp (g * g) ((e - 1) / 2) * g

val from_naive_exp: g:nat -> e:nat -> Lemma
  (ensures (nexp g e = exp g e)) (decreases e)
let rec from_naive_exp g e = match e with
  | 0 -> ()
  | 1 -> ()
  | _ ->
    if e % 2 = 0
    then begin
      from_naive_exp (g * g) (e/2);
      nexp_exp g 2 (e/2)
    end
    else begin
      from_naive_exp (g * g) ((e-1)/2);
      nexp_exp g 2 ((e-1)/2);
      nexp_mul1 g (((e-1)/2)*2) 1
    end

val exp_bigger_than_base: g:nat -> e:nat -> Lemma (g > 0 /\ e > 0 ==> exp g e >= g)
  [SMTPat (exp g e)]
let exp_bigger_than_base g0 e0 =
  nexp_bigger_than_base g0 e0;
  from_naive_exp g0 e0

val exp_zero: e:pos -> Lemma (exp 0 e = 0)
let rec exp_zero e = nexp_zero e; from_naive_exp 0 e

val exp_one1: g:nat -> Lemma (ensures (exp g one = g)) [SMTPat (exp g one)]
let exp_one1 _ = ()

val exp_one2: e:nat -> Lemma (ensures (exp one e = one)) [SMTPat (exp one e)]
let rec exp_one2 e = nexp_one2 e; from_naive_exp one e

val exp_mul1: g:nat -> e1:nat -> e2:nat -> Lemma
  (exp g e1 * exp g e2 = exp g (e1 + e2))
let exp_mul1 g e1 e2 =
  nexp_mul1 g e1 e2;
  from_naive_exp g e1;
  from_naive_exp g e2;
  from_naive_exp g (e1+e2)

val exp_add: g:nat -> e1:nat -> e2:nat{e2 >= e1} -> Lemma
  (exp g e1 + exp g e2 = exp g e1 * (1 + exp g (e2 - e1)))
let exp_add g e1 e2 =
  exp_mul1 g e1 (e2 - e1);
  distributivity_add_right (exp g e1) 1 (exp g (e2 - e1))

val exp_sub: g:nat -> e1:nat -> e2:nat{e2 >= e1} -> Lemma
  (exp g e1 - exp g e2 = exp g e1 * (1 - exp g (e2 - e1)))
let exp_sub g e1 e2 =
  exp_mul1 g e1 (e2 - e1);
  distributivity_sub_right (exp g e1) 1 (exp g (e2 - e1))

val exp_order_lemma: g:pos -> e1:nat -> e2:nat{e1 <= e2} -> Lemma
  (exp g e1 <= exp g e2)
let rec exp_order_lemma g e1 e2 =
  if e2 = e1 then () else begin
    exp_order_lemma g e1 (e2-1);
    from_naive_exp g e2;
    assert (exp g e1 <= exp g (e2-1));
    multiplication_order_lemma g 1 (exp g (e2-1));
    assert (exp g e1 <= exp g (e2-1) * g);
    exp_mul1 g (e2-1) 1
  end

val exp_order_lemma_strict: g:nat{g>1} -> e1:nat -> e2:nat{e1 < e2} -> Lemma
  (exp g e1 < exp g e2)
let rec exp_order_lemma_strict g e1 e2 =
  if e2 = e1 then () else begin
    exp_order_lemma g e1 (e2-1);
    from_naive_exp g e2;
    assert (exp g e1 <= exp g (e2-1));
    multiplication_order_lemma g 1 (exp g (e2-1));
    assert (exp g e1 <= exp g (e2-1) * g);
    exp_mul1 g (e2-1) 1
  end

val exp_greater_than_power: g:pos{g>1} -> e:nat -> Lemma (exp g e > e)
let exp_greater_than_power g e =
  nexp_greater_than_power g e; from_naive_exp g e

// Naive modular exp
val nmexp: #n:big -> fe n -> e:nat -> Tot (fe n) (decreases e)
let rec nmexp #n g e = match e with
  | 0 -> 1
  | 1 -> g
  | _ -> g *% nmexp g (e-1)

val nmexp_eq_arg1: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (requires (g1 = g2))
  (ensures (nmexp g1 e = nmexp g2 e))
let nmexp_eq_arg1 #n _ _ _ = ()

val nmexp_zero: #n:big -> e:pos -> Lemma
  (nmexp #n 0 e = 0)
let rec nmexp_zero #n e = match e with
  | 1 -> ()
  | _ -> nmexp_zero #n (e-1)

val nmexp_one1: #n:big -> g:fe n -> Lemma
  (ensures (nmexp g one = g))
  [SMTPat (nmexp g one)]
let nmexp_one1 #n _ = ()

val nmexp_one2: #n:big -> e:nat -> Lemma
  (ensures (nmexp #n one e = one))
  [SMTPat (nmexp #n one e)]
let rec nmexp_one2 #n e = match e with
  | 0 -> ()
  | _ ->  nmexp_one2 #n (e-1)

val nmexp_mul1: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (nmexp g e1 *% nmexp g e2 = nmexp g (e1 + e2))
let rec nmexp_mul1 #n g e1 e2 = match e2 with
  | 0 -> assert(nmexp g e2 = one)
  | 1 -> assert(nmexp g e2 = g)
  | _ -> nmexp_mul1 g e1 (e2-1)

val nmexp_mul2: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (ensures (nmexp (g1 *% g2) e = nmexp g1 e *% nmexp g2 e))
  (decreases e)
let rec nmexp_mul2 #n g1 g2 e = match e with
  | 0 -> ()
  | 1 -> mul_one #n one
  | _ -> begin
    nmexp_mul2 #n g1 g2 (e-1);
    mul4_assoc g1 g2 (nmexp g1 (e-1)) (nmexp g2 (e-1))
  end

val nmexp_exp: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (ensures ((nmexp (nmexp g e1) e2) = (nmexp g (e1 * e2))))
  (decreases e2)
let rec nmexp_exp #n g e1 e2 = match e2 with
  | 0 -> if (nmexp g e1) = 0 then () else nmexp_zero #n (nmexp g e1)
  | _ -> begin
    nmexp_mul1 g e1 (e1 * e2 - e1);
    distributivity_sub_right e1 e2 1;
    nmexp_exp #n g e1 (e2 - 1)
  end

// To subgroup
val to_fe_nmexp1: #n:big -> k:pos{n % k = 0 && n / k > 1 } -> g:fe n -> e:nat -> Lemma
  (to_fe #(n/k) (nmexp g e) = nmexp (to_fe #(n/k) g) e)
let rec to_fe_nmexp1 #n k g e = match e with
  | 0 -> ()
  | 1 -> ()
  | _ -> begin
    let m = n / k in
    lemma_div_mod n k;
    assert (n = k * m);
    modulo_modulo_lemma (g * nmexp g (e-1)) m k;
    assert (((g * nmexp g (e-1)) % n) % m = (g * nmexp g (e-1)) % m);
    assert ((g *% nmexp g (e-1)) % m = (g * nmexp g (e-1)) % m);
    assert (to_fe #m (g *% nmexp g (e-1)) = to_fe #m (g * nmexp g (e-1)));
    to_fe_nmexp1 #n k g (e-1);
    to_fe_mul #m g (nmexp g (e-1))
  end


// Define mexp' for composite n and for unit g.
val mexp: #n:big -> fe n -> e:nat -> Tot (fe n) (decreases e)
let rec mexp #n g e =
  if e = 1 then g
  else if e = 0 then 1
  else
     if e % 2 = 0
     then mexp (g *% g) (e / 2)
     else mexp (g *% g) ((e - 1) / 2) *% g

val mexp_eq_nmexp: #n:big -> g:fe n -> e:nat -> Lemma
  (ensures (nmexp g e = mexp g e)) (decreases e)
let rec mexp_eq_nmexp #n g e = match e with
  | 0 -> ()
  | 1 -> ()
  | _ ->
    if e % 2 = 0
    then begin
      mexp_eq_nmexp #n (g *% g) (e/2);
      nmexp_exp #n g 2 (e/2)
    end
    else begin
      mexp_eq_nmexp #n (g *% g) ((e-1)/2);
      nmexp_exp g 2 ((e-1)/2)
    end

val mexp_two_is_sqr: #n:big -> g:fe n -> Lemma
  (mexp g 2 = sqr g)
let mexp_two_is_sqr #n _ = ()

val mexp_one1: #n:big -> g:fe n -> Lemma
  (ensures (mexp g one = g))
  [SMTPat (mexp g one)]
let mexp_one1 #n _ = ()

val mexp_one2: #n:big -> e:nat -> Lemma
  (ensures (mexp #n one e = one))
  [SMTPat (mexp #n one e)]
let mexp_one2 #n e = mexp_eq_nmexp #n one e; nmexp_one2 #n e

val mexp_zero1: #n:big -> e:pos -> Lemma
  (mexp #n 0 e = 0)
let mexp_zero1 #n e = mexp_eq_nmexp #n 0 e; nmexp_zero #n e

val mexp_zero2: #n:big -> g:fe n{g <> 0} -> Lemma
  (mexp #n g 0 = 1)
let mexp_zero2 #n _ = ()

val mexp_mul1: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (mexp g e1 *% mexp g e2 = mexp g (e1 + e2))
let mexp_mul1 #n g e1 e2 =
  mexp_eq_nmexp g e1;
  mexp_eq_nmexp g e2;
  mexp_eq_nmexp g (e1+e2);
  nmexp_mul1 g e1 e2

val mexp_mul2: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (mexp (g1 *% g2) e = mexp g1 e *% mexp g2 e)
let mexp_mul2 #n g1 g2 e =
  mexp_eq_nmexp (g1 *% g2) e;
  mexp_eq_nmexp g1 e;
  mexp_eq_nmexp g2 e;
  nmexp_mul2 g1 g2 e

val mexp_exp: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (mexp #n (mexp #n g e1) e2 = mexp #n g (e1 * e2))
let mexp_exp #n g e1 e2 =
  mexp_eq_nmexp g e1;
  mexp_eq_nmexp (nmexp g e1) e2;
  mexp_eq_nmexp g (e1 * e2);
  nmexp_exp g e1 e2

val mexp_add: #n:big -> g:fe n -> e1:nat -> e2:nat{e2 >= e1} -> Lemma
  (mexp g e1 +% mexp g e2 = mexp g e1 *% (1 +% mexp g (e2 - e1)))
let mexp_add #n g e1 e2 =
  mexp_mul1 g e1 (e2 - e1);
  mul_one (mexp g e1);
  mul_add_distr_r (mexp g e1) 1 (mexp g (e2 - e1))

val mexp_sub: #n:big -> g:fe n -> e1:nat -> e2:nat{e2 >= e1} -> Lemma
  (mexp g e1 -% mexp g e2 = mexp g e1 *% (1 -% mexp g (e2 - e1)))
let mexp_sub #n g e1 e2 =
  mexp_mul1 g e1 (e2 - e1);
  mul_one (mexp g e1);
  mul_sub_distr_r (mexp g e1) 1 (mexp g (e2 - e1))

val to_fe_mexp1: #n:big -> k:pos{n % k = 0 && n / k > 1 } -> g:fe n -> e:nat -> Lemma
  (to_fe #(n/k) (mexp g e) = mexp (to_fe #(n/k) g) e)
let rec to_fe_mexp1 #n k g e =
  to_fe_nmexp1 #n k g e;
  mexp_eq_nmexp g e;
  mexp_eq_nmexp (to_fe #(n/k) g) e


(* Inverses *)

val isunit: #n:big -> a:fe n -> Type0
let isunit #n a = exists (b:fe n). a *% b = 1

val isunit_nonzero: #n:big -> g:fe n -> Lemma (isunit g ==> g <> 0)
let isunit_nonzero #n g =
  assert (g = 0 ==> (forall x. g * x = 0));
  assert (g = 0 ==> (forall x. (g * x) % n = 0))

val one_isunit: n:big -> Lemma (isunit #n 1)
let one_isunit _ = ()

val inv_unique: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a *% b = one /\ a *% c = one) ==> b = c)
let inv_unique #n a b c =

  let l (): Lemma (requires ((a *% b = one /\ a *% c = one)))
                  (ensures (b = c)) =
           calc (==) {
             c; =={} c *% one; =={} c *% (a *% b); =={}
                     (c *% a) *% b; =={} one *% b; =={} b;
           }
          in

  move_requires l ()

#reset-options "--z3rlimit 50"

val inv_as_gcd1: #n:big -> a:fe n{a>0} -> Lemma
  (requires (is_gcd a n 1))
  (ensures (isunit a))
let inv_as_gcd1 #n a =
  let (g,u,v) = ex_eucl a n in
  //gcd_prop_subdiv a n g;
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
  assert ((to_fe #n u *% a) = 1)

#reset-options

val inv_as_gcd2: #n:big -> a:fe n{a>0} -> Lemma
  (requires (isunit a))
  (ensures (is_gcd a n 1))
let inv_as_gcd2 #n a =
  let l (): Lemma (exists (b:fe n). a *% b = 1) = () in
  exists_elim (gcd a n = 1) #(fe n) #(fun (b:fe n) -> a *% b = 1) (l ()) (fun u -> begin
    mod_prop n (u*a) 1;
    assert ((u * a) + (-((u*a)/n)*n) = 1);
    neg_mul_left ((u*a)/n) n;
    ex_eucl_lemma3 a n u (-(u*a)/n)
  end)

val inv_as_gcd: #n:big -> a:fe n{a>0} -> Lemma
  (isunit a <==> gcd a n = 1)
let inv_as_gcd #n a =
  move_requires inv_as_gcd1 a;
  move_requires inv_as_gcd2 a

#reset-options "--z3rlimit 50"

val isunit_in_prime_field: #p:prm -> a:fe p{a > 0} -> Lemma (isunit a)
let isunit_in_prime_field #p a =
  gcd_with_prime p a;
  inv_as_gcd1 a

val finv0: #n:big -> a:fe n -> b:fe n
let finv0 #n a =
  if a = 0 then 0 else
  let (g,u,v) = ex_eucl a n in
  if g <> 1 then 0 else to_fe #n u

val finv0_prop: #n:big -> a:fe n -> Lemma
  (let b = finv0 #n a in
   (isunit a <==> b *% a = one) /\
   (~(isunit a) <==> b = 0))
  [SMTPat (finv0 #n a)]
let finv0_prop #n a =
  if a = 0 then () else
  let (g,u,v) = ex_eucl a n in
  assert (gcd a n = g);
  inv_as_gcd a;
  if g <> 1 then () else begin
    modulo_distributivity (u*a) (v*n) n;
    multiple_modulo_lemma v n;
    lemma_mod_twice (u * a) n;
    to_fe_idemp #n 1;
    to_fe_idemp a;
    to_fe_mul #n u a
  end

#reset-options

val finv: #n:big -> a:fe n{isunit a} -> b:fe n{b *% a = one}
let finv #n a = finv0 a

val finv_unique: #n:big -> a:fe n -> b:fe n -> Lemma
  ((a *% b = one) ==> (b = finv a))
let finv_unique #n a b =
  let l (): Lemma (requires ((a *% b = one))) (ensures (isunit a /\ b = finv a)) =
          inv_unique #n a b (finv a) in

  move_requires l ()

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

// Unit to any power is still a unit
val isunit_mexp: #n:big -> g:fe n -> x:nat -> Lemma
  (requires (isunit g))
  (ensures (isunit (mexp g x)))
let rec isunit_mexp #n g x =
  isunit_nonzero g;
  if x = 0 then (mexp_zero2 #n g; one_isunit n) else
  if x = 1 then mexp_one1 g else begin
    isunit_mexp #n g (x-1);
    mul4_assoc (mexp g (x-1)) (finv (mexp g (x-1))) g (finv g);
    mexp_one1 #n g;
    mexp_mul1 g (x-1) 1
  end

val zerodiv_is_nonunit: #n:big -> a:fe n -> b:fe n -> Lemma
  ((b > 0 /\ a *% b = 0) ==> (~(isunit a)))
let zerodiv_is_nonunit #n a b =
  let l1 (): Lemma (requires b > 0 /\ a *% b = 0 /\ isunit a) (ensures False) = begin
    let a' = finv a in
    to_fe_idemp #n 1;
    assert ((a *% a') +% (a *% b) = 1);
    mul_add_distr_r a a' b;
    assert (a *% (a' +% b) = 1);

    let l' (): Lemma (requires a' +% b = a') (ensures b = 0) = begin
      assert ((a' +% b) -% a' = a' -% a');
      add_comm a' b;
      add_assoc b a' (neg a');
      add_sub_zero b
    end in

    move_requires l' ();
    assert (a' +% b <> a');
    finv_unique a (a' +% b) // found two different inverses
  end in
  move_requires l1 ()

// F_p has no zero divisors.
val prime_field_zerodivs: #p:prm -> a:fe p{a>0} -> b:fe p{b>0} -> Lemma
  (a *% b <> 0)
let prime_field_zerodivs #p a b =
  gcd_with_prime p a;
  inv_as_gcd1 #p a;
  zerodiv_is_nonunit #p a b;
  assert (a *% b <> 0)

type is_mult_order (#n:big) (g:fe n{isunit g}) (r:pos) =
    mexp g r = one /\ (forall (x:pos{x<r}). mexp g x <> one)

val mul_zero_either: #n:big -> a:fe n -> b:fe n -> Lemma
  (isunit a /\ a *% b = 0 ==> b = 0)
let mul_zero_either #n a b = zerodiv_is_nonunit #n a b

val mult_order_unique: #n:big -> g:fe n{isunit g} -> r1:pos -> r2:pos -> Lemma
  ((is_mult_order g r1 /\ is_mult_order g r2) ==> r1 = r2)
let mult_order_unique #n g r1 r2 = ()

val divides_exactly_one_multiple: a:big -> b:nat -> c:pos -> Lemma
  (requires (divides a (b*c) /\ is_gcd a c 1))
  (ensures (divides a b))
let divides_exactly_one_multiple a b c =
  assert (a == c ==> is_gcd a c a);
  gcd_mod_reduce a c;
  gcd_mod_nonzero a c 1;
  assert (is_gcd (c % a) a 1);
  gcd_symm (c % a) a 1;
  assert ((b * c) % a = 0);
  modulo_mul_distributivity b c a;
  assert (((b % a) * (c % a)) % a = 0);
  let b' = to_fe #a b in
  let c' = to_fe #a c in
  assert (b' *% c' = 0);
  inv_as_gcd1 #a c';
  mul_zero_either  c' b'

(*** Predicate on lists, all_distinct ***)

// nat less or equal than
// Same as fe n, but for nat (not for big)
type nlet (n:nat) = x:nat{x < n}


val cons_shifts_index_value: #a:eqtype -> x:a -> l:list a -> Lemma
  (ensures (forall (i:nat{i < L.length l}). L.index (x::l) (i+1) = L.index l i))
  (decreases (L.length l))
let rec cons_shifts_index_value #a x l = match l with
  | [] -> ()
  | (x::xs) -> cons_shifts_index_value #a x xs

val map_preserves_order: #a:eqtype -> #b:eqtype -> p:(a -> b) -> l:list a -> Lemma
  (forall (i:nat{i < L.length l}). L.index (L.map p l) i = p (L.index l i))
let rec map_preserves_order #a #b p l = match l with
  | [] -> ()
  | x::xs -> begin
      let l' = L.map p l in
      let x' = p x in
      let xs' = L.map p xs in
      assert (L.index l' 0 = p (L.index l 0));
      map_preserves_order p xs;
      cons_shifts_index_value x xs;
      cons_shifts_index_value x' xs';
      assert (L.length xs + 1 = L.length l);
      assert (forall (i:nat{i < L.length xs}). L.index xs' i = p (L.index xs i));
      assert (forall (i:nat{i < L.length xs}). L.index l' (i+1) = L.index xs' i);
      assert (forall (i:nat{i < L.length xs}). L.index l' (i+1) = p (L.index l (i+1)));
      assert (forall (i:nat{i < L.length l - 1}). L.index l' (i+1) = p (L.index l (i+1)));

      let lemma1 (i:nat{i < L.length l - 1}): Lemma (L.index l' (i+1) = p (L.index l (i+1))) = () in
      let lemma2 (i:nat{i > 0 /\ i < L.length l}): Lemma (L.index l' i = p (L.index l i)) = lemma1 (i-1) in

      forall_intro lemma2
    end


type forall_l (#a:eqtype) (l:list a) (p: a -> Type0) =
  forall (i:nlet (L.length l)). p (L.index l i)

type forall_l2 (#a:eqtype) (l:list a) (p: a -> a -> Type0) =
  forall (i:nlet (L.length l)) (j:nlet (L.length l){i <> j}). p (L.index l i) (L.index l j)

// Weaker definition in general, but same for the symmetric p
type forall_l2' (#a:eqtype) (l:list a) (p: a -> a -> Type0) =
  forall (i:nlet (L.length l)) (j:nlet (L.length l){i > j}). p (L.index l i) (L.index l j)

type pred_symm (#a:eqtype) (p:a -> a -> Type0) = forall (x:a) (y:a). p x y <==> p y x

// l2' is weaker than l2
val forall_l2_to_weaker: #a:eqtype -> l:list a -> p:(a -> a -> Type0) -> Lemma
  (forall_l2 l p ==> forall_l2' l p)
let forall_l2_to_weaker #a l p =
  let n = L.length l in

  let l_right (): Lemma (requires (forall_l2 l p)) (ensures (forall_l2' l p)) = begin
    let l1 (i:nlet n): Lemma (forall (j:nlet n{i <> j}). p (L.index l i) (L.index l j)) = () in
    let l2 (i:nlet n): Lemma (forall (j:nlet n{i > j}). p (L.index l i) (L.index l j)) = l1 i in
    forall_intro l2
  end in

  move_requires l_right ()

// In case of symm function, they are equivalent
val forall_l2_symm: #a:eqtype -> l:list a -> p:(a -> a -> Type0){pred_symm #a p} -> Lemma
  (forall_l2 l p <==> forall_l2' l p)
let forall_l2_symm #a l p =
  let n = L.length l in

  forall_l2_to_weaker l p;

  let l_left (): Lemma (requires (forall_l2' l p)) (ensures (forall_l2 l p)) = begin
    let l1 (i:nlet n) (j:nlet n{i > j}): Lemma (p (L.index l i) (L.index l j)) = () in
    let l2 (i:nlet n): Lemma (forall (j:nlet n{i <> j}). p (L.index l i) (L.index l j)) =
      let l22 (j:nlet n{j <> i}): Lemma (p (L.index l i) (L.index l j)) =
        if i > j then l1 i j else l1 j i
      in forall_intro l22
    in forall_intro l2
  end in

  move_requires l_left ()

val forall_l2_tail: #a:eqtype -> l:list a{L.length l > 0} -> p:(a -> a -> Type0) -> Lemma
  (requires (forall_l2 l p))
  (ensures (forall_l2 (L.tail l) p))
let forall_l2_tail #a l p =
  let (x::xs) = l in
  cons_shifts_index_value x xs

type all_distinct (#a:eqtype) (l:list a) = forall_l2 l (fun x y -> x <> y)
type all_distinct2 (#a:eqtype) (l:list a) = forall_l2' l (fun x y -> x <> y)

val distinct_defs_equiv: #a:eqtype -> l:list a -> Lemma
  (all_distinct l <==> all_distinct2 l)
let distinct_defs_equiv #a l = forall_l2_symm l (fun x y -> x <> y)

// Fstar struggles to infer some basic statments sometimes.
val all_distinct_expand: #a:eqtype -> l:list a -> Lemma
  (all_distinct l <==>
   (forall (i:nlet (L.length l)) (j:nlet (L.length l){i <> j}). L.index l i <> L.index l j))
let all_distinct_expand #a l = ()

val all_distinct_negation: #a:eqtype -> l:list a -> Lemma
  (~(all_distinct l) <==>
   (exists (i:nlet (L.length l)) (j:nlet (L.length l){i <> j}). L.index l i = L.index l j))
let all_distinct_negation #a l = ()

// int in between
type ibtw (a:int) (b:int{b >= a}) = x:int{x >= a /\ x <= b}

type is_int_range a (b:int{b >= a}) (l: list (ibtw a b)) =
  L.length l = b - a + 1 /\
  (forall (i:nat{i <= b - a}). L.index l i = i + a)

type int_range (a:int) (b:int{b >= a}) = l:list (ibtw a b) { is_int_range a b l }

val range_list:
      a:int
   -> b:int{b >= a}
   -> Tot (l:int_range a b)
      (decreases (b - a))
let rec range_list a b =
  let rec create (b0:int{a <= b0 /\ b0 <= b}):
          Tot (res:list (ibtw a b)
               { L.length res = b - b0 + 1
               /\ (forall (i:nat{i <= b - b0}). L.index res i = b0 + i)
               })
              (decreases (b - b0))
          =
    if b0 = b then [b] else begin
      let l0 = create (b0 + 1) in
      let index_l0 (i:nat{i <= b - b0 - 1}): Lemma (L.index l0 i = b0 + 1 + i) = () in
      let index_l0_2 (i:pos{i <= b - b0}): Lemma (L.index l0 (i-1) = b0 + i) = index_l0 (i-1) in
      let l1 = b0 :: l0 in
      cons_shifts_index_value b0 l0;
      assert (forall (i:nat{i < b - b0}). L.index l1 (i+1) = L.index l0 i);
      assert (forall (i:pos{i <= b - b0}). L.index l1 i = L.index l0 (i-1));
      forall_intro index_l0_2;
      assert (forall (i:pos{i <= b - b0}). L.index l1 i = b0 + i);
      assert (forall (i:nat{i <= b - b0}). L.index l1 i = b0 + i);
      l1
    end in

  create a

// Find a minimum, then find an element bigger than minimum for
// n times, and show that the last element is bigger than
// higher bound. ??
val dirichlet_collision: #a:int -> #b:int{b >= a} -> l:list (ibtw a b){ L.length l > b - a + 1 } ->
        t:tuple2 (nlet (b-a+1)) (nlet (b-a+1))
        { let (i,j) = t in (assert (i<L.length l); i <> j /\ L.index l i = L.index l j) }
let dirichlet_collision #a #b l = admit ()

val collision_means_nondistinct:
     #a:eqtype
  -> l:list a
  -> i:nlet (L.length l)
  -> j:nlet (L.length l){j <> i}
  -> Lemma (requires (L.index l i = L.index l j))
           (ensures (~(all_distinct l)))
let collision_means_nondistinct #a l i j =
  exists_intro_2_dep #(nlet (L.length l)) #(fun i -> j:nlet (L.length l){i <> j}) (fun i j -> L.index l i = L.index l j) i j;
  assert (exists (i:nlet (L.length l)) (j:nlet (L.length l){i <> j}). L.index l i = L.index l j);
  all_distinct_negation l

val dirichlet_nondistinct:
     #a:int
  -> #b:int{b >= a}
  -> l:list (ibtw a b){ L.length l > b-a+1 }
  -> Lemma (~(all_distinct l))
let dirichlet_nondistinct #a #b l =
  let (i,j) = dirichlet_collision l in
  assert (i <> j /\ L.index l i = L.index l j);
  let k = L.length l in
  let i':nlet k = i in
  let j':nlet k = j in
  assert (L.index l i' = L.index l j');
  collision_means_nondistinct l i' j'

val dirichlet_fe1: #n:big -> l:list (x:fe n{x>0}){ L.length l >= n } -> Lemma (~(all_distinct l))
let dirichlet_fe1 #n l =
  let p x = x in
  let l':(t:list (ibtw 1 (n-1)){ L.length t > (n-1) - 1 + 1 }) = L.map p l in
  let (i,j) = dirichlet_collision #1 #(n-1) l' in
  let i':nlet (L.length l) = i in
  let j':nlet (L.length l) = j in
  map_preserves_order p l;
  collision_means_nondistinct l i' j'

val equiv_foralls: #n:big -> g:fe n{isunit g /\ g > 1} -> Lemma
  (requires (forall (i:pos{i<=n}) (j:pos{j<=n/\i<>j}). mexp g i <> mexp g j))
  (ensures (forall (i:nlet n) (j:nlet n{i<>j}). mexp g (i+1) <> mexp g (j+1)))
let equiv_foralls #n g =
  let l0 (i:pos{i<=n}) (j:pos{j<=n/\i<>j}): Lemma (mexp g i <> mexp g j) = () in
  let l1 (i:nlet n) (j:nlet n{i<>j}): Lemma (mexp g (i+1) <> mexp g (j+1)) = l0 (i+1) (j+1) in
  forall_intro_2 l1


(*** Unit powers collision, mult_order ***)

val replace_quantor_var: #a:eqtype -> #b:eqtype -> p:(x:a -> y:a{x <> y} -> bool) -> Lemma
  (requires (a == b /\ (forall (x:a) (y:a{x <> y}).p x y)))
  (ensures (forall (x:b) (y:b{x <> y}). p x y))
let replace_quantor_var #a #b p = ()

val conclude_distinct: #n:big -> l:list (x:fe n{x > 0}){L.length l = n} -> Lemma
  (requires (forall (i:nlet n) (j:nlet n{i <> j}). L.index l i <> L.index l j))
  (ensures (all_distinct l))
let conclude_distinct #n l =
  all_distinct_expand l;
  assert (forall (i:nlet n) (j:nlet n{i <> j}). L.index l i <> L.index l j);

  let p (i:nlet n) (j:nlet n{j <> i}) = L.index l i <> L.index l j in
  assert (nlet n == nlet (L.length l));
  assert (forall (i:nlet n) (j:nlet n{i <> j}). p i j);
  replace_quantor_var #(nlet n) #(nlet (L.length l)) p;

  assert (forall (i:nlet (L.length l)) (j:nlet (L.length l){i <> j}). L.index l i <> L.index l j)

val unit_powers_collide_inv: #n:big -> g:fe n{isunit g /\ g > 1} -> Lemma
  (requires (forall (i:pos{i<=n}) (j:pos{j<=n/\i<>j}). mexp g i <> mexp g j))
  (ensures False)
let unit_powers_collide_inv #n g =
  let l0 = range_list 1 n in
  assert (forall (i:nlet n). L.index l0 i = i+1);
  let p (i:pos{i<=n}):(x:fe n{x > 0}) =
    isunit_mexp g i;
    isunit_nonzero (mexp g i);
    mexp g i in
  let l: list (x:fe n{x > 0}) = L.map p l0 in
  assert (L.length l = n);
  map_preserves_order p l0;
  assert (forall (i:nlet n). L.index l i = mexp g (i+1));

  equiv_foralls g;
  assert (forall (i:nlet n) (j:nlet n{i <> j}). mexp g (i+1) <> mexp g (j+1));
  assert (forall (i:nlet n) (j:nlet n{i <> j}). L.index l i <> L.index l j);
  conclude_distinct l;
  assert (all_distinct l);
  dirichlet_fe1 l

val unit_powers_collide: #n:big -> g:fe n{isunit g /\ g > 1} -> Lemma
  (exists (i:pos{i <= n}) (j:pos{j <= n /\ i <> j}). mexp g i = mexp g j)
let unit_powers_collide #n g = move_requires unit_powers_collide_inv g

val unit_powers_collide_strict: #n:big -> g:fe n{isunit g /\ g > 1} -> Lemma
  (exists (i:pos{i <= n}) (j:pos{j <= n /\ i < j}). mexp g i = mexp g j)
let unit_powers_collide_strict #n g =

  unit_powers_collide g;

  let ex1: squash (exists (i:pos{i <= n}) (j:pos{j <= n /\ i <> j}). mexp g i = mexp g j) = () in

  let p_less (i:pos{i <= n}) (j:pos{j <= n /\ i < j}): Type = mexp g i = mexp g j in
  let goal = exists (i:pos{i <= n}) (j:pos{j <= n /\ i < j}). mexp g i = mexp g j in

  let l'' (i:pos{i <= n}) (j:pos{j <= n /\ i <> j /\ mexp g i = mexp g j}):
          squash (exists (i:pos{i <= n}) (j:pos{j <= n /\ i < j}). mexp g i = mexp g j) = begin
    if i < j then exists_intro_2_dep p_less i j else exists_intro_2_dep p_less j i
  end in
  exists_elim_pair_dep goal ex1 l''

val unit_powers_collide_strict_inv: #n:big -> g:fe n{isunit g /\ g > 1} -> Lemma
  (requires (forall (i:pos{i <= n}) (j:pos{j <= n /\ i < j}). mexp g i <> mexp g j))
  (ensures False)
let unit_powers_collide_strict_inv #n g = move_requires unit_powers_collide_strict g

val find_unit_colliding_powers: #n:big -> g:fe n{isunit g /\ g > 1} ->
  res:(tuple2 pos pos){ let (i,j) = res in j <= n /\ i < j /\ mexp g i = mexp g j }
let find_unit_colliding_powers #n g =

  let goalcond ((i,j):(tuple2 pos pos)) = (j <= n /\ i < j /\ mexp g i = mexp g j) in
  let goal = res:(tuple2 pos pos){ goalcond res } in

  let rec look1 (i:pos{i<n /\ (forall (i':pos{i'<=n/\i'>i}) (j':pos{j'<=n /\ i'<j'}).
                                       (mexp g i' <> mexp g j'))}):
                goal = begin

    let rec look2 (j:pos{j > i /\ j <= n /\ (forall (j':pos{j'<=n /\ j'>j}). mexp g j' <> mexp g i)}):
                  k:option pos{ match k with
                                | None -> (forall (j':pos{j'<=n/\j'>i}). mexp g j' <> mexp g i)
                                | Some j' -> j' > i /\ j' <= n /\ mexp g j' = mexp g i } = begin
      if mexp g j = mexp g i
      then Some j
      else (if j = i+1 then None else look2 (j-1))
    end in

    let look2res = look2 n in
    match look2res with
      | Some (j:pos) -> begin
          assert (goalcond (i,j));
          let k:(t:(tuple2 pos pos){goalcond t}) = (i,j) in
          k
        end
      | None -> begin
          if i > 1 then look1 (i-1) else begin
            assert (forall (i':pos{i'<=n}) (j':pos{j'<=n /\ i' < j'}). mexp g i' <> mexp g j');
            unit_powers_collide_strict_inv g
          end
        end
  end in

  look1 (n-1)


val power_leading_to_one_exists: #n:big -> g:fe n{isunit g} -> Lemma
  (exists (r':pos{r'<=n}). mexp g r' = 1)
let power_leading_to_one_exists #n g =

  let l (): Lemma (requires (g > 1 /\ (forall (r':pos{r' <= n}). mexp g r' <> 1))) (ensures False) = begin
    assert (forall (r':pos{r' <= n}). mexp g r' <> 1);

    let l11 (i:pos) (j:pos): Lemma (requires j < i /\ i <= n /\ mexp g i = mexp g j)
                                   (ensures False) = begin
        // g ^ i - g^j = g^i (1 - g^(j-1)) = 0
        // g^i /= 0, so g^(j-i) = 1
        // which contradicts that no element is zero
        isunit_mexp g i;
        if i <> 1 then begin
          mexp_sub g j i;
          assert (mexp g i *% (1 -% mexp g (i - j)) = 0);
          isunit_nonzero (mexp g i);
          mul_zero_either (mexp g i) (1 -% mexp g (i-j));
          assert (1 -% mexp g (i-j) = 0);
          add_move_to_right 1 (mexp g (i-j)) 0;
          add_sub_zero (mexp g (i-j));
          assert (1 = mexp g (i-j))
        end
    end in

    let ltype i j = ((j<i/\i<=n/\mexp g i = mexp g j) ==> False) in
    let l12 (i:pos): (j:pos) -> Lemma (ltype i j) = fun j -> move_requires (l11 i) j in
    let l13 (): (i:pos) -> Lemma (forall (j:pos). ltype i j) =
      fun i -> forall_intro #pos #_ (l12 i) in
    forall_intro #pos #_ (l13 ());

    assert (forall (i:pos) (j:pos). ltype i j);
    assert (forall (i:pos{i <= n}) (j:pos{j<i}). mexp g i = mexp g j ==> False);
    unit_powers_collide_strict g
  end in move_requires l ();

  isunit_nonzero g;
  mexp_one1 g


val mult_order_exists: #n:big -> g:fe n{isunit g} -> Lemma
  (exists (r:pos). r<=n /\ is_mult_order g r)
let mult_order_exists #n g =
  let goal = (exists (r:pos). r <= n /\ is_mult_order g r) in

  let rec test_possible (r:pos{r<=n /\ mexp g r = one}): Lemma goal = begin
    assert ((forall (x:pos{x<r}). mexp g x <> one) ==> goal);
    assert (~(forall (x:pos{x<r}). mexp g x <> one) ==> (exists (x:pos{x<r}). mexp g x = one));

    let l (): Lemma (requires (~(forall (x:pos{x<r}). mexp g x <> one)))
                    (ensures goal) = begin
      let ex_internal: squash (exists (x:pos{x<r}). mexp g x = one) = () in
      let elim_statement (x:pos{x<r /\ mexp g x = one}): GTot (squash goal) = test_possible x in
      exists_elim goal ex_internal elim_statement
    end in
    move_requires l ()
  end in

  let exprev: squash (exists (r':pos). r' <= n /\ mexp g r' = 1) = power_leading_to_one_exists g in

  exists_elim goal exprev (fun x -> test_possible x; assert (goal))

val comp_mult_order_loop:
     #n:big
  -> g:fe n{isunit g}
  -> r_test:pos{ r_test <= n /\ (forall (r':pos{r' < r_test}). mexp g r' <> 1) }
  -> Tot (r:pos {is_mult_order g r})
         (decreases (n - r_test))
let rec comp_mult_order_loop #n g r_test =
  if mexp g r_test = 1 then r_test
  else begin
    if r_test < n then comp_mult_order_loop g (r_test + 1) else begin
      mult_order_exists g;
      assert (forall (r':pos{r' <= n}). mexp g r' <> 1);
      assert (False);
      0
    end
  end

val mult_order:
     #n:big
  -> g:fe n{isunit g}
  -> r:pos {is_mult_order g r}
let mult_order #n g = comp_mult_order_loop g 1

val mult_order_less: #n:big -> g:fe n{isunit g} -> e:pos -> Lemma
  (mexp g e = 1 ==> mult_order g <= e)
let mult_order_less #n g e = ()

val g_pow_order_reduc_raw:
     #n:big
  -> g:fe n{isunit g /\ g > 0}
  -> x:nat
  -> r:pos{is_mult_order g r}
  -> Lemma
  (ensures (mexp g x = mexp g (x % r)))
  (decreases x)
let rec g_pow_order_reduc_raw #n g x r =
  if x < r
  then modulo_lemma x r
  else begin
    lemma_div_mod x r;
    mexp_exp g r (x/r);
    mexp_mul1 g (r * (x/r)) (x%r);
    mexp_one2 #n (x/r)
  end

val g_pow_order_reduc: #n:big -> g:fe n{isunit g /\ g > 0} -> x:nat -> Lemma
  (ensures (mexp g x = mexp g (x % mult_order g)))
  (decreases x)
let rec g_pow_order_reduc #n g x = g_pow_order_reduc_raw g x (mult_order g)

val g_pow_inverse_raw: #n:big -> g:fe n{isunit g} -> x:nat -> r:pos{is_mult_order g r} -> Lemma
  (isunit (mexp g x) /\
   finv (mexp g x) = mexp g (r - (x % r)))
let g_pow_inverse_raw #n g x r =
  isunit_nonzero #n g;
  if x = 0
  then begin
    mexp_zero2 g;
    zero_mod_n r
  end else
    let x' = x % r in
    modulo_range_lemma x r;
    let inv_e = r - x' in
    assert(inv_e >= 0 && inv_e <= r);
    assert(mexp g r = one);
    g_pow_order_reduc_raw g x r;
    mexp_mul1 g x' inv_e;
    assert(mexp g x' *% mexp g (r - x') = one);
    assert(mexp g x *% mexp g (r - x') = one);
    finv_unique (mexp g x) (mexp g (r - x'))

val mult_order_and_one1: #n:big -> g:fe n{isunit g} -> e:pos -> Lemma
  (requires divides (mult_order g) e)
  (ensures mexp g e = 1)
let mult_order_and_one1 #n g e =
  let r = mult_order g in
  mod_prop r e 0;
  swap_mul (e / r) r;
  mexp_exp g r (e/r);
  mexp_one2 #n (e/r)

val mult_order_and_one2: #n:big -> g:fe n{isunit g} -> e:pos -> Lemma
  (requires mexp g e = 1)
  (ensures divides (mult_order g) e)
let mult_order_and_one2 #n g e =
  let r = mult_order g in
  let l (): Lemma (requires (~(divides r e))) (ensures False) = begin
    g_pow_order_reduc g e;
    assert (mexp g e = mexp g (e % r));
    assert (mexp g (e % r) = 1)
  end in
  move_requires l ()

val mult_order_and_one: #n:big -> g:fe n{isunit g} -> e:pos -> Lemma
  (mexp g e = 1 <==> divides (mult_order g) e)
let mult_order_and_one #n g e =
  let r = mult_order g in
  let l1 (): Lemma (requires divides r e) (ensures mexp g e = 1) = mult_order_and_one1 g e in
  let l2 (): Lemma (requires mexp g e = 1) (ensures divides r e) = mult_order_and_one2 g e in
  move_requires l1 ();
  move_requires l2 ()


val g_pow_inverse: #n:big -> g:fe n{isunit g} -> x:nat -> Lemma
  (let r = mult_order g in
   isunit (mexp g x) /\
   finv (mexp g x) = mexp g (r - (x % r)))
let g_pow_inverse #n g x = g_pow_inverse_raw g x (mult_order g)

val g_pow_isunit: #n:big -> g:fe n -> x:nat -> Lemma
  (requires (isunit g))
  (ensures (isunit (mexp g x)))
let g_pow_isunit #n g x = g_pow_inverse g x

val g_pow_isunit_rev: #n:big -> g:fe n -> x:pos -> Lemma
  (requires (isunit (mexp g x)))
  (ensures (isunit g))
let g_pow_isunit_rev #n g x =
  mexp_one1 g;
  if x > 1 then begin
    let y = finv (mexp g x) in
    assert (mexp g x *% y = 1);
    mexp_mul1 g (x-1) 1;
    assert (g *% (mexp g (x-1) *% y) = 1)
  end

#reset-options "--z3rlimit 50"

val mult_order_of_mexp: #n:big -> g:fe n{isunit g} -> e1:pos -> e2:pos -> Lemma
  (requires is_mult_order g (e1 * e2))
  (ensures (g_pow_isunit g e1; is_mult_order (mexp g e1) e2))
let mult_order_of_mexp #n g e1 e2 =
  g_pow_isunit g e1;
  mexp_exp g e1 e2;
  assert (mexp (mexp g e1) e2 = one);

  let l (e3:pos{e3 < e2}): Lemma (requires (mexp (mexp g e1) e3 = one))
                                 (ensures False) = begin
      mexp_exp g e1 e3;
      assert (mexp g (e1 * e3) = one);
      multiplication_order_lemma_strict e3 e2 e1;
      assert (e1 * e3 < e1 * e2);
      assert (~(is_mult_order g (e1 * e2)));
      assert (False)
    end in

  let l' (e3:pos{e3 < e2}): Lemma (mexp (mexp g e1) e3 = one ==> False) = begin
      move_requires l e3
    end in

  forall_intro l'

#reset-options


(*** Factorisation, euler's thm ***)

// Prime power factorisation
type factorisation =
  l:list (tuple2 prm pos)
  { forall_l2 l (fun (p1,_) (p2,_) -> p1 <> p2) }

val f_combine: factorisation -> pos
let rec f_combine l = match l with
  | [] -> 1
  | ((p,e)::xs) ->
    forall_l2_tail l (fun (p1,_) (p2,_) -> p1 <> p2);
    exp p e * f_combine xs

val p_fact: p:prm -> f:factorisation{L.length f = 1}
let p_fact p = [(p,1)]

val p_fact_lemma: p:prm -> Lemma
  (f_combine (p_fact p) = p)
  [SMTPat (p_fact p)]
let p_fact_lemma p = ()

val pq_fact: p:prm -> q:prm{p<>q} -> f:factorisation{L.length f = 2}
let pq_fact p q = [(p,1);(q,1)]

val pq_fact_lemma: p:prm -> q:prm{p<>q} -> Lemma
  (f_combine (pq_fact p q) = p*q)
  [SMTPat (pq_fact p q)]
let pq_fact_lemma p q = ()

val pe_fact: p:prm -> e:pos -> f:factorisation{L.length f = 1}
let pe_fact p e = [(p,e)]

val pe_fact_lemma: p:prm -> e:pos -> Lemma
  (f_combine (pe_fact p e) = exp p e)
  [SMTPat (pq_fact p e)]
let pe_fact_lemma p e = ()

val totient_prm: p:prm -> r:pos -> phi:nat{phi > 1}
let totient_prm p r =
  exp_sub p (r-1) r;
  exp p r - exp p (r-1)

val carm:
     f:factorisation{L.length f > 0}
  -> pos
let rec carm f =
  forall_l2_tail f (fun (p1,_) (p2,_) -> p1 <> p2);
  let ((p,r)::xs) = f in
  let phi = totient_prm p r in
  let cur =
         if (p % 2 = 0 && p > 4)
         then phi / 2
         else phi
  in if xs = [] then cur else lcm cur (carm xs)

val carm_p: p:prm -> c:fe p{c >= 1 /\ carm [(p,1)] = c }
let carm_p p = p - 1

val carm_p_is_carm: p:prm -> Lemma
  (carm_p p = carm [(p,1)])
  [SMTPat (carm_p p)]
let carm_p_is_carm p = ()

val carm_pq: p:prm -> q:prm{p <> q} -> l:fe (p*q){l <= (p-1) * (q-1) /\ l >= 1}
let carm_pq p q = lcm_less_mul (p-1) (q-1); lcm (p-1) (q-1)

val carm_pq_is_carm: p:prm -> q:prm{p <> q} -> Lemma
  (carm_pq p q =  carm (pq_fact p q))
let carm_pq_is_carm p q = ()

val carm_pe: p:prm -> e:pos -> l:fe (exp p e){l <= exp p e /\ l >= 1}
let carm_pe p e =
  let phi = totient_prm p e in
  if (p % 2 = 0 && p > 4) then phi / 2 else phi

val carm_pe_is_carm: p:prm -> e:pos -> Lemma
  (carm_pe p e =  carm (pe_fact p e))
let carm_pe_is_carm p q = ()

// This is a basic property of carmichael function.
val euler_thm:
     n:big
  -> f:factorisation{f_combine f = n}
  -> cm:pos{cm = carm f}
  -> a:fe n
  -> Lemma
  (isunit a ==> mexp a cm = 1)
let euler_thm _ _ _ = admit()

val flt: #p:prm -> a:fe p{a>0} -> Lemma (mexp a (p-1) = 1)
let flt #p a =
  isunit_in_prime_field a;
  euler_thm p [(p,1)] (p-1) a
