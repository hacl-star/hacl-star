module FStar.Math.Euclid

open FStar.Mul
open FStar.Math.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

val divides_refl (a:int) : Lemma (a `divides` a) [SMTPat (a `divides` a)]
let divides_refl a =
  Classical.exists_intro (fun q -> a = q * a) 1

val divides_0 (a:int) : Lemma (a `divides` 0)
let divides_0 a =
  Classical.exists_intro (fun q -> 0 = q * a) 0

val divides_1 (a:int) : Lemma (requires a `divides` 1) (ensures a = 1 \/ a = -1)
let divides_1 a = ()

val divides_minus (a b:int) : Lemma
  (requires a `divides` b)
  (ensures  a `divides` (-b))
  [SMTPat (a `divides` (-b))]
let divides_minus a b =
  Classical.exists_elim (a `divides` (-b))
    (Squash.get_proof (a `divides` b))
    (fun q -> Classical.exists_intro (fun q' -> -b = q' * a) (-q))

val divides_opp (a b:int) : Lemma
  (requires a `divides` b)
  (ensures (-a) `divides` b)
let divides_opp a b =
  Classical.exists_elim ((-a) `divides` b)
    (Squash.get_proof (a `divides` b))
    (fun q -> Classical.exists_intro (fun q' -> b = q' * (-a)) (-q))

///
/// Properties of `is_gcd`
///

val is_gcd_sym (a b d:int) : Lemma
  (requires is_gcd a b d)
  (ensures  is_gcd b a d)
let is_gcd_sym a b d = ()

val is_gcd_0 (a:int) : Lemma (is_gcd a 0 a)
let is_gcd_0 a = ()

val is_gcd_1 (a:int) : Lemma (is_gcd a 1 1)
let is_gcd_1 a = ()

val is_gcd_refl (a:int) : Lemma (is_gcd a a a)
let is_gcd_refl a = ()

val opp_idempotent (a:int) : Lemma (-(-a) == a)
let opp_idempotent a = ()

val is_gcd_minus (a b d:int) : Lemma
  (requires is_gcd a (-b) d)
  (ensures  is_gcd b a d)
let is_gcd_minus a b d =
  opp_idempotent b;
  divides_minus d (-b)

val is_gcd_opp (a b d:int) : Lemma
  (requires is_gcd a b d)
  (ensures  is_gcd b a (-d))
let is_gcd_opp a b d =
  divides_opp d a;
  divides_opp d b

val eq_mult_left (a b:int) : Lemma (requires a = b * a) (ensures a = 0 \/ b = 1)
let eq_mult_left a b = ()

val eq_mult_one (a b:int) : Lemma 
  (requires a * b = 1) 
  (ensures (a = 1 /\ b = 1) \/ (a = -1 /\ b = -1))
let eq_mult_one a b = ()

val divide_antisym (a b:int) : Lemma
  (requires a `divides` b /\ b `divides` a)
  (ensures  a = b \/ a = -b)
let divide_antisym a b =
  if a <> 0 then
    Classical.exists_elim (a = b \/ a = -b) (Squash.get_proof (exists q1. b = q1 * a))
      (fun q1 ->
        Classical.exists_elim (a = b \/ a = -b) (Squash.get_proof (exists q2. a = q2 * b))
          (fun q2 ->
            assert (b = q1 * a);
            assert (a = q2 * b);
            assert (b = q1 * (q2 * b));
            paren_mul_right q1 q2 b;
            eq_mult_left b (q1 * q2);
            eq_mult_one q1 q2))


let is_gcd_unique a b c d =
  assert (d `divides` c);
  assert (c `divides` d);
  divide_antisym c d


val divides_plus (a b d:int) : Lemma
  (requires d `divides` a /\ d `divides` b)
  (ensures  d `divides` (a + b))
let divides_plus a b d =
  Classical.exists_elim (d `divides` (a + b)) (Squash.get_proof (exists q1. a = q1 * d))
    (fun q1 ->
      Classical.exists_elim (d `divides` (a + b)) (Squash.get_proof (exists q2. b = q2 * d))
        (fun q2 ->
          assert (a + b = q1 * d + q2 * d);
          distributivity_add_left q1 q2 d;
          Classical.exists_intro (fun q -> a + b = q * d) (q1 + q2)))

val divides_sub (a b d:int) : Lemma
  (requires d `divides` a /\ d `divides` b)
  (ensures  d `divides` (a - b))
  [SMTPat (d `divides` (a - b))]
let divides_sub a b d =
  divides_plus a (-b) d

val divides_mult_right (a b d:int) : Lemma
  (requires d `divides` b)
  (ensures  d `divides` (a * b))
  [SMTPat (d `divides` (a * b))]
let divides_mult_right a b d =
  Classical.exists_elim (d `divides` (a * b)) (Squash.get_proof (d `divides` b))
    (fun q ->
      paren_mul_right a q d;
      Classical.exists_intro (fun r -> a * b = r * d) (a * q))

val add_sub_idempotent (a b:int) : Lemma (a - b + b = a)
let add_sub_idempotent a b = ()

val is_gcd_for_euclid (a b q d:int) : Lemma
  (requires is_gcd b (a - q * b) d)
  (ensures  is_gcd a b d)
  [SMTPat (is_gcd b (a - q * b) d)]
let is_gcd_for_euclid a b q d =
  add_sub_idempotent a (q * b);
  Classical.exists_elim (d `divides` a) (Squash.get_proof (exists r. a = r * d + q * b))
    (fun r ->
      divides_mult_right r d d ;
      divides_mult_right q b d ;
      divides_plus (r * d) (q * b) d)


val egcd (a b u1 u2 u3 v1 v2 v3:int) : Pure (int & int & int)
  (requires v3 >= 0 /\
            u1 * a + u2 * b = u3 /\
            v1 * a + v2 * b = v3 /\
            (forall d. is_gcd u3 v3 d ==> is_gcd a b d))
  (ensures (fun (u, v, d) -> u * a + v * b = d /\ is_gcd a b d))
  (decreases v3)
let rec egcd a b u1 u2 u3 v1 v2 v3 =
  if v3 = 0 then
    begin
    divides_0 u3;
    (u1, u2, u3)
    end
  else
    begin
    let q = u3 / v3 in
    euclidean_division_definition u3 v3;
    assert (u3 - q * v3 = (q * v3 + u3 % v3) - q * v3);
    assert (q * v3 - q * v3 = 0);
    swap_add_plus_minus (q * v3) (u3 % v3) (q * v3);
    calc (==) {
      (u1 - q * v1) * a + (u2 - q * v2) * b;
      == { _ by (FStar.Tactics.Canon.canon()) }
      (u1 * a + u2 * b) - q * (v1 * a + v2 * b);
      == { }
      u3 - q * v3;
      == { }
      u3 % v3;
    };
    let u1, v1 = v1, u1 - q * v1 in
    let u2, v2 = v2, u2 - q * v2 in
    let u3, v3 = v3, u3 - q * v3 in
    egcd a b u1 u2 u3 v1 v2 v3
    end


let euclid_gcd a b =
  if b >= 0 then
    egcd a b 1 0 a 0 1 b
  else 
    begin
    Classical.forall_intro (Classical.move_requires (is_gcd_minus a b));
    egcd a b 1 0 a 0 (-1) (-b)
    end

val is_gcd_prime_aux (p:pos) (a:pos{a < p}) (d:int) : Lemma
  (requires is_prime p /\ d `divides` p /\ d `divides` a)
  (ensures  d = 1 \/ d = -1)
let is_gcd_prime_aux p a d = 
  ()

val is_gcd_prime (p:pos{is_prime p}) (a:pos{a < p}) : Lemma (is_gcd p a 1)
let is_gcd_prime p a =
  Classical.forall_intro (Classical.move_requires (is_gcd_prime_aux p a));
  assert (forall x. x `divides` p /\ x `divides` a ==> x = 1 \/ x = -1 /\ x `divides` 1)

#push-options "--using_facts_from '* -FStar.Math.Euclid'"

let bezout_prime p a =
  let r, s, d = euclid_gcd p a in
  assert (r * p + s * a = d);
  assert (is_gcd p a d);
  is_gcd_prime p a;
  is_gcd_unique p a 1 d;
  if d = 1 then r, s else -r, -s

let euclid n a b r s =
  let open FStar.Math.Lemmas in
  calc (==) {
    b % n;
    == { distributivity_add_left (r * n) (s * a) b }
    (r * n * b + s * a * b) % n;
    == { paren_mul_right s a b }
    (r * n * b + s * (a * b)) % n;
    == { modulo_distributivity (r * n * b) (s * (a * b)) n }
    ((r * n * b) % n + s * (a * b) % n) % n;
    == { lemma_mod_mul_distr_r s (a * b) n }
    ((r * n * b) % n + s * ((a * b) % n) % n) % n;
    == { assert (a * b % n = 0) }
    ((r * n * b) % n + s * 0 % n) % n;
    == { assert (s * 0 == 0) }
    ((r * n * b) % n + 0 % n) % n;
    == { modulo_lemma 0 n }
    ((r * n * b) % n) % n;
    == { lemma_mod_twice (r * n * b) n }
    (r * n * b) % n;
    == { swap_mul r n; paren_mul_right n r b }
    (n * (r * b)) % n;
    == { lemma_mod_mul_distr_l n (r * b) n}
    n % n * (r * b) % n;
    == { assert (n % n = 0) }
    (0 * (r * b)) % n;
    == { assert (0 * (r * b) == 0) }
    0 % n;
    == { modulo_lemma 0 n }
    0;
  }
