module Lib.NatMod

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val pow_mod_ (#m:pos) (a:nat_mod m) (b:pos) : Tot (nat_mod m) (decreases b)
let rec pow_mod_ #m a b =
  if b = 1 then a
  else
    if b % 2 = 0 then pow_mod_ (mul_mod a a) (b / 2)
    else mul_mod a (pow_mod_ (mul_mod a a) (b / 2))

let pow_mod #m a b = pow_mod_ #m a b

#push-options "--fuel 2"
let lemma_pow0 a = ()

let lemma_pow1 a = ()

let lemma_pow_unfold a b = ()
#pop-options

let rec lemma_pow_greater a b =
  if b = 0 then lemma_pow0 a
  else begin
    lemma_pow_unfold a b;
    lemma_pow_greater a (b - 1) end


let rec lemma_pow_add x n m =
  if n = 0 then lemma_pow0 x
  else begin
    lemma_pow_unfold x n;
    lemma_pow_unfold x (n + m);
    lemma_pow_add x (n-1) m;
    Math.Lemmas.paren_mul_right x (pow x (n-1)) (pow x m) end


let rec lemma_pow_double a b =
  if b = 0 then begin
    lemma_pow0 (a * a);
    lemma_pow0 a end
  else begin
    calc (==) {
      pow (a * a) b;
      (==) { lemma_pow_unfold (a * a) b }
      a * a * pow (a * a) (b - 1);
      (==) { lemma_pow_double a (b - 1) }
      a * a * pow a (b + b - 2);
      (==) { lemma_pow1 a }
      pow a 1 * pow a 1 * pow a (b + b - 2);
      (==) { lemma_pow_add a 1 1 }
      pow a 2 * pow a (b + b - 2);
      (==) { lemma_pow_add a 2 (b + b - 2) }
      pow a (b + b);
    };
    assert (pow (a * a) b == pow a (b + b))
  end


let rec lemma_pow_mul_base a b n =
  if n = 0 then begin
    lemma_pow0 a;
    lemma_pow0 b;
    lemma_pow0 (a * b) end
  else begin
    calc (==) {
      pow a n * pow b n;
      (==) { lemma_pow_unfold a n; lemma_pow_unfold b n }
      a * pow a (n - 1) * (b * pow b (n - 1));
      (==) { Math.Lemmas.paren_mul_right (a * pow a (n - 1)) b (pow b (n - 1)) }
      a * pow a (n - 1) * b * pow b (n - 1);
      (==) { }
      a * b * pow a (n - 1) * pow b (n - 1);
      (==) { Math.Lemmas.paren_mul_right (a * b) (pow a (n - 1)) (pow b (n - 1)) }
      a * b * (pow a (n - 1) * pow b (n - 1));
      (==) { lemma_pow_mul_base a b (n - 1) }
      a * b * pow (a * b) (n - 1);
      (==) { lemma_pow_unfold (a * b) n }
      pow (a * b) n;
    };
    assert (pow a n * pow b n == pow (a * b) n)
  end


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


#push-options "--fuel 2"
val lemma_pow_mod1: #n:pos -> a:nat_mod n -> Lemma (pow_mod #n a 1 == a)
let lemma_pow_mod1 #n a = ()

val lemma_pow_mod_unfold0: n:pos -> a:nat_mod n -> b:pos{1 < b /\ b % 2 = 0} -> Lemma
  (pow_mod #n a b == pow_mod (mul_mod a a) (b / 2))
let lemma_pow_mod_unfold0 n a b = ()

val lemma_pow_mod_unfold1: n:pos -> a:nat_mod n -> b:pos{1 < b /\ b % 2 = 1} -> Lemma
  (pow_mod #n a b == mul_mod a (pow_mod (mul_mod a a) (b / 2)))
let lemma_pow_mod_unfold1 n a b = ()
#pop-options

val lemma_pow_mod_: n:pos -> a:nat_mod n -> b:pos -> Lemma
  (ensures (pow_mod #n a b == pow a b % n))
  (decreases b)

let rec lemma_pow_mod_ n a b =
  if b = 1 then begin
    lemma_pow1 a;
    lemma_pow_mod1 a end
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
