module FStar.Math.Euclid

open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let divides (a b:int) : prop = exists q. b = q * a

let is_gcd (a b d:int) : prop =
  d `divides` a /\
  d `divides` b /\
  (forall x. (x `divides` a /\ x `divides` b) ==> x `divides` d)

val is_gcd_unique (a b c d:int) : Lemma
  (requires is_gcd a b c /\ is_gcd a b d)
  (ensures  c = d \/ c = -d)

val euclid_gcd (a b:int) : Pure (int & int & int)
  (requires True)
  (ensures  fun (u, v, d) -> u * a + v * b = d /\ is_gcd a b d)

let is_prime (p:pos) =
  forall (d:int).{:pattern (d `divides` p)}
    (d `divides` p ==> (d = 1 \/ d = -1 \/ d = p \/ d = -p))

val bezout_prime (p:pos) (a:pos{a < p}) : Pure (int & int)
  (requires is_prime p)
  (ensures  fun (r, s) -> r * p + s * a = 1)

val euclid (n:pos) (a b r s:int) : Lemma
  (requires (a * b) % n = 0 /\ r * n + s * a = 1)
  (ensures  b % n = 0)
