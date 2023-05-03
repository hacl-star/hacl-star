module Lib.NatMod

module LE = Lib.Exponentiation.Definition

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

#push-options "--fuel 2"
let lemma_pow0 a = ()

let lemma_pow1 a = ()

let lemma_pow_unfold a b = ()
#pop-options

let rec lemma_pow_gt_zero a b =
  if b = 0 then lemma_pow0 a
  else begin
    lemma_pow_unfold a b;
    lemma_pow_gt_zero a (b - 1) end


let rec lemma_pow_ge_zero a b =
  if b = 0 then lemma_pow0 a
  else begin
    lemma_pow_unfold a b;
    lemma_pow_ge_zero a (b - 1) end


let rec lemma_pow_nat_is_pow a b =
  let k = mk_nat_comm_monoid in
  if b = 0 then begin
    lemma_pow0 a;
    LE.lemma_pow0 k a end
  else begin
    lemma_pow_unfold a b;
    lemma_pow_nat_is_pow a (b - 1);
    LE.lemma_pow_unfold k a b;
    () end


let lemma_pow_zero b =
  lemma_pow_unfold 0 b


let lemma_pow_one b =
  let k = mk_nat_comm_monoid in
  LE.lemma_pow_one k b;
  lemma_pow_nat_is_pow 1 b


let lemma_pow_add x n m =
  let k = mk_nat_comm_monoid in
  LE.lemma_pow_add k x n m;
  lemma_pow_nat_is_pow x n;
  lemma_pow_nat_is_pow x m;
  lemma_pow_nat_is_pow x (n + m)


let lemma_pow_mul x n m =
  let k = mk_nat_comm_monoid in
  LE.lemma_pow_mul k x n m;
  lemma_pow_nat_is_pow x n;
  lemma_pow_nat_is_pow (pow x n) m;
  lemma_pow_nat_is_pow x (n * m)


let lemma_pow_double a b =
  let k = mk_nat_comm_monoid in
  LE.lemma_pow_double k a b;
  lemma_pow_nat_is_pow (a * a) b;
  lemma_pow_nat_is_pow a (b + b)


let lemma_pow_mul_base a b n =
  let k = mk_nat_comm_monoid in
  LE.lemma_pow_mul_base k a b n;
  lemma_pow_nat_is_pow a n;
  lemma_pow_nat_is_pow b n;
  lemma_pow_nat_is_pow (a * b) n


let rec lemma_pow_mod_base a b n =
  if b = 0 then begin
    lemma_pow0 a;
    lemma_pow0 (a % n) end
  else begin
    calc (==) {
      pow a b % n;
      (==) { lemma_pow_unfold a b }
      a * pow a (b - 1) % n;
      (==) { Math.Lemmas.lemma_mod_mul_distr_r a (pow a (b - 1)) n }
      a * (pow a (b - 1) % n) % n;
      (==) { lemma_pow_mod_base a (b - 1) n }
      a * (pow (a % n) (b - 1) % n) % n;
      (==) { Math.Lemmas.lemma_mod_mul_distr_r a (pow (a % n) (b - 1)) n }
      a * pow (a % n) (b - 1) % n;
      (==) { Math.Lemmas.lemma_mod_mul_distr_l a (pow (a % n) (b - 1)) n }
      a % n * pow (a % n) (b - 1) % n;
      (==) { lemma_pow_unfold (a % n) b }
      pow (a % n) b % n;
    };
    assert (pow a b % n == pow (a % n) b % n)
  end



let lemma_mul_mod_one #m a = ()

let lemma_mul_mod_assoc #m a b c =
  calc (==) {
    (a * b % m) * c % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c m }
    (a * b) * c % m;
    (==) { Math.Lemmas.paren_mul_right a b c }
    a * (b * c) % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (b * c) m }
    a * (b * c % m) % m;
    }

let lemma_mul_mod_comm #m a b = ()

let pow_mod #m a b = pow_mod_ #m a b

let pow_mod_def #m a b = ()


#push-options "--fuel 2"
val lemma_pow_mod0: #n:pos{1 < n} -> a:nat_mod n -> Lemma (pow_mod #n a 0 == 1)
let lemma_pow_mod0 #n a = ()

val lemma_pow_mod_unfold0: n:pos{1 < n} -> a:nat_mod n -> b:pos{b % 2 = 0} -> Lemma
  (pow_mod #n a b == pow_mod (mul_mod a a) (b / 2))
let lemma_pow_mod_unfold0 n a b = ()

val lemma_pow_mod_unfold1: n:pos{1 < n} -> a:nat_mod n -> b:pos{b % 2 = 1} -> Lemma
  (pow_mod #n a b == mul_mod a (pow_mod (mul_mod a a) (b / 2)))
let lemma_pow_mod_unfold1 n a b = ()
#pop-options


val lemma_pow_mod_: n:pos{1 < n} -> a:nat_mod n -> b:nat -> Lemma
  (ensures (pow_mod #n a b == pow a b % n))
  (decreases b)

let rec lemma_pow_mod_ n a b =
  if b = 0 then begin
    lemma_pow0 a;
    lemma_pow_mod0 a end
  else begin
    if b % 2 = 0 then begin
      calc (==) {
	pow_mod #n a b;
	(==) { lemma_pow_mod_unfold0 n a b }
	pow_mod #n (mul_mod #n a a) (b / 2);
	(==) { lemma_pow_mod_ n (mul_mod #n a a) (b / 2) }
	pow (mul_mod #n a a) (b / 2) % n;
	(==) { lemma_pow_mod_base (a * a) (b / 2) n }
	pow (a * a) (b / 2) % n;
	(==) { lemma_pow_double a (b / 2) }
	pow a b % n;
      };
      assert (pow_mod #n a b == pow a b % n) end
    else begin
      calc (==) {
	pow_mod #n a b;
	(==) { lemma_pow_mod_unfold1 n a b }
	mul_mod a (pow_mod (mul_mod #n a a) (b / 2));
	(==) { lemma_pow_mod_ n (mul_mod #n a a) (b / 2) }
	mul_mod a (pow (mul_mod #n a a) (b / 2) % n);
	(==) { lemma_pow_mod_base (a * a) (b / 2) n }
	mul_mod a (pow (a * a) (b / 2) % n);
	(==) { lemma_pow_double a (b / 2) }
	mul_mod a (pow a (b / 2 * 2) % n);
	(==) { Math.Lemmas.lemma_mod_mul_distr_r a (pow a (b / 2 * 2)) n }
	a * pow a (b / 2 * 2) % n;
	(==) { lemma_pow1 a }
	pow a 1 * pow a (b / 2 * 2) % n;
	(==) { lemma_pow_add a 1 (b / 2 * 2) }
	pow a (b / 2 * 2 + 1) % n;
	(==) { Math.Lemmas.euclidean_division_definition b 2 }
	pow a b % n;
	};
      assert (pow_mod #n a b == pow a b % n) end
  end

let lemma_pow_mod #n a b = lemma_pow_mod_ n a b


let rec lemma_pow_nat_mod_is_pow #n a b =
  let k = mk_nat_mod_comm_monoid n in
  if b = 0 then begin
    lemma_pow0 a;
    LE.lemma_pow0 k a end
  else begin
    calc (==) {
      pow a b % n;
      (==) { lemma_pow_unfold a b }
      a * pow a (b - 1) % n;
      (==) { Math.Lemmas.lemma_mod_mul_distr_r a (pow a (b - 1)) n }
      a * (pow a (b - 1) % n) % n;
      (==) { lemma_pow_nat_mod_is_pow #n a (b - 1) }
      a * LE.pow k a (b - 1) % n;
      (==) { }
      k.LE.mul a (LE.pow k a (b - 1));
      (==) { LE.lemma_pow_unfold k a b }
      LE.pow k a b;
      }; () end


let lemma_add_mod_one #m a =
  Math.Lemmas.small_mod a m


let lemma_add_mod_assoc #m a b c =
  calc (==) {
    add_mod (add_mod a b) c;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (a + b) c m }
    ((a + b) + c) % m;
    (==) { }
    (a + (b + c)) % m;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r a (b + c) m }
    add_mod a (add_mod b c);
  }


let lemma_add_mod_comm #m a b = ()


let lemma_mod_distributivity_add_right #m a b c =
  calc (==) {
    mul_mod a (add_mod b c);
    (==) { }
    a * ((b + c) % m) % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (b + c) m }
    a * (b + c) % m;
    (==) { Math.Lemmas.distributivity_add_right a b c }
    (a * b + a * c) % m;
    (==) { Math.Lemmas.modulo_distributivity (a * b) (a * c) m }
    add_mod (mul_mod a b) (mul_mod a c);
    }


let lemma_mod_distributivity_add_left #m a b c =
  lemma_mod_distributivity_add_right c a b


let lemma_mod_distributivity_sub_right #m a b c =
  calc (==) {
    mul_mod a (sub_mod b c);
    (==) { }
    a * ((b - c) % m) % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (b - c) m }
    a * (b - c) % m;
    (==) { Math.Lemmas.distributivity_sub_right a b c }
    (a * b - a * c) % m;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (a * b) (- a * c) m }
    (mul_mod a b - a * c) % m;
    (==) { Math.Lemmas.lemma_mod_sub_distr (mul_mod a b) (a * c) m }
    sub_mod (mul_mod a b) (mul_mod a c);
    }


let lemma_mod_distributivity_sub_left #m a b c =
  lemma_mod_distributivity_sub_right c a b


let lemma_inv_mod_both #m a b =
  let p1 = pow a (m - 2) in
  let p2 = pow b (m - 2) in

  calc (==) {
    mul_mod (inv_mod a) (inv_mod b);
    (==) { lemma_pow_mod #m a (m - 2); lemma_pow_mod #m b (m - 2) }
    p1 % m * (p2 % m) % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l p1 (p2 % m) m }
    p1 * (p2 % m) % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r p1 p2 m }
    p1 * p2 % m;
    (==) { lemma_pow_mul_base a b (m - 2) }
    pow (a * b) (m - 2) % m;
    (==) { lemma_pow_mod_base (a * b) (m - 2) m }
    pow (mul_mod a b) (m - 2) % m;
    (==) { lemma_pow_mod #m (mul_mod a b) (m - 2) }
    inv_mod (mul_mod a b);
    }


#push-options "--fuel 1"
val pow_eq: a:nat -> n:nat -> Lemma (Fermat.pow a n == pow a n)
let rec pow_eq a n =
  if n = 0 then ()
  else pow_eq a (n - 1)
#pop-options


let lemma_div_mod_prime #m a =
  Math.Lemmas.small_mod a m;
  assert (a == a % m);
  assert (a <> 0 /\ a % m <> 0);

  calc (==) {
    pow_mod #m a (m - 2) * a % m;
    (==) { lemma_pow_mod #m a (m - 2) }
    pow a (m - 2) % m * a % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (pow a (m - 2)) a m }
    pow a (m - 2) * a % m;
    (==) { lemma_pow1 a; lemma_pow_add a (m - 2) 1 }
    pow a (m - 1) % m;
    (==) { pow_eq a (m - 1) }
    Fermat.pow a (m - 1) % m;
    (==) { Fermat.fermat_alt m a }
    1;
    }


let lemma_div_mod_prime_one #m a =
  lemma_pow_mod #m 1 (m - 2);
  lemma_pow_one (m - 2);
  Math.Lemmas.small_mod 1 m


let lemma_div_mod_prime_cancel #m a b c =
  calc (==) {
    mul_mod (mul_mod a c) (inv_mod (mul_mod c b));
    (==) { lemma_inv_mod_both c b }
    mul_mod (mul_mod a c) (mul_mod (inv_mod c) (inv_mod b));
    (==) { lemma_mul_mod_assoc (mul_mod a c) (inv_mod c) (inv_mod b) }
    mul_mod (mul_mod (mul_mod a c) (inv_mod c)) (inv_mod b);
    (==) { lemma_mul_mod_assoc a c (inv_mod c) }
    mul_mod (mul_mod a (mul_mod c (inv_mod c))) (inv_mod b);
    (==) { lemma_div_mod_prime c }
    mul_mod (mul_mod a 1) (inv_mod b);
    (==) { Math.Lemmas.small_mod a m }
    mul_mod a (inv_mod b);
    }


let lemma_div_mod_prime_to_one_denominator #m a b c d =
  calc (==) {
    mul_mod (div_mod a c) (div_mod b d);
    (==) { }
    mul_mod (mul_mod a (inv_mod c)) (mul_mod b (inv_mod d));
    (==) {
      lemma_mul_mod_comm #m b (inv_mod d);
      lemma_mul_mod_assoc #m (mul_mod a (inv_mod c)) (inv_mod d) b }
    mul_mod (mul_mod (mul_mod a (inv_mod c)) (inv_mod d)) b;
    (==) { lemma_mul_mod_assoc #m a (inv_mod c) (inv_mod d) }
    mul_mod (mul_mod a (mul_mod (inv_mod c) (inv_mod d))) b;
    (==) { lemma_inv_mod_both c d }
    mul_mod (mul_mod a (inv_mod (mul_mod c d))) b;
    (==) {
      lemma_mul_mod_assoc #m a (inv_mod (mul_mod c d)) b;
      lemma_mul_mod_comm #m (inv_mod (mul_mod c d)) b;
      lemma_mul_mod_assoc #m a b (inv_mod (mul_mod c d)) }
    mul_mod (mul_mod a b) (inv_mod (mul_mod c d));
    }


val lemma_div_mod_eq_mul_mod1: #m:prime -> a:nat_mod m -> b:nat_mod m{b <> 0} -> c:nat_mod m ->
  Lemma (div_mod a b = c ==> a = mul_mod c b)

let lemma_div_mod_eq_mul_mod1 #m a b c =
  if div_mod a b = c then begin
    assert (mul_mod (div_mod a b) b = mul_mod c b);
    calc (==) {
      mul_mod (div_mod a b) b;
      (==) { lemma_div_mod_prime_one b }
      mul_mod (div_mod a b) (div_mod b 1);
      (==) { lemma_div_mod_prime_to_one_denominator a b b 1 }
      div_mod (mul_mod a b) (mul_mod b 1);
      (==) { lemma_div_mod_prime_cancel a 1 b }
      div_mod a 1;
      (==) { lemma_div_mod_prime_one a }
      a;
      } end
  else ()


val lemma_div_mod_eq_mul_mod2: #m:prime -> a:nat_mod m -> b:nat_mod m{b <> 0} -> c:nat_mod m ->
  Lemma (a = mul_mod c b ==> div_mod a b = c)

let lemma_div_mod_eq_mul_mod2 #m a b c =
  if a = mul_mod c b then begin
    assert (div_mod a b == div_mod (mul_mod c b) b);
    calc (==) {
      div_mod (mul_mod c b) b;
      (==) { Math.Lemmas.small_mod b m }
      div_mod (mul_mod c b) (mul_mod b 1);
      (==) { lemma_div_mod_prime_cancel c 1 b }
      div_mod c 1;
      (==) { lemma_div_mod_prime_one c }
      c;
    } end
  else ()


let lemma_div_mod_eq_mul_mod #m a b c =
  lemma_div_mod_eq_mul_mod1 a b c;
  lemma_div_mod_eq_mul_mod2 a b c


val lemma_mul_mod_zero2: n:pos -> x:int -> y:int -> Lemma
  (requires x % n == 0 \/ y % n == 0)
  (ensures  x * y % n == 0)

let lemma_mul_mod_zero2 n x y =
  if x % n = 0 then
    Math.Lemmas.lemma_mod_mul_distr_l x y n
  else
    Math.Lemmas.lemma_mod_mul_distr_r x y n


let lemma_mul_mod_prime_zero #m a b =
  Classical.move_requires_3 Euclid.euclid_prime m a b;
  Classical.move_requires_3 lemma_mul_mod_zero2 m a b


val lemma_pow_mod_prime_zero_: #m:prime -> a:nat_mod m -> b:pos -> Lemma
  (requires pow a b % m = 0)
  (ensures  a = 0)

let rec lemma_pow_mod_prime_zero_ #m a b =
  if b = 1 then lemma_pow1 a
  else begin
    let r1 = pow a (b - 1) % m in
    lemma_pow_unfold a b;
    assert (a * pow a (b - 1) % m = 0);
    Math.Lemmas.lemma_mod_mul_distr_r a (pow a (b - 1)) m;
    lemma_mul_mod_prime_zero #m a r1;
    //assert (a = 0 \/ r1 = 0);
    if a = 0 then () else lemma_pow_mod_prime_zero_ #m a (b - 1) end


let lemma_pow_mod_prime_zero #m a b =
  lemma_pow_mod #m a b;
  Classical.move_requires_2 lemma_pow_mod_prime_zero_ a b;
  Classical.move_requires lemma_pow_zero b


val lemma_div_mod_is_zero1: #m:pos{2 < m} -> a:nat_mod m -> b:nat_mod m -> Lemma
  (requires a = 0 || b = 0)
  (ensures  div_mod a b = 0)

let lemma_div_mod_is_zero1 #m a b =
  if a = 0 then ()
  else begin
    lemma_pow_mod #m b (m - 2);
    lemma_pow_zero (m - 2) end

val lemma_div_mod_prime_is_zero2: #m:prime{2 < m} -> a:nat_mod m -> b:nat_mod m -> Lemma
  (requires div_mod a b = 0)
  (ensures  a = 0 || b = 0)

let lemma_div_mod_prime_is_zero2 #m a b =
  lemma_mul_mod_prime_zero a (inv_mod b);
  assert (a = 0 || inv_mod b = 0);
  lemma_pow_mod_prime_zero #m b (m - 2)


let lemma_div_mod_prime_is_zero #m a b =
  Classical.move_requires_2 lemma_div_mod_is_zero1 a b;
  Classical.move_requires_2 lemma_div_mod_prime_is_zero2 a b
