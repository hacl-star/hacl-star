module Lib.NatMod

module LE = Lib.Exponentiation

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



let lemma_one_mod #m a = ()

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


val pow_mod_ (#m:pos) (a:nat_mod m) (b:pos) : Tot (nat_mod m) (decreases b)
let rec pow_mod_ #m a b =
  if b = 1 then a
  else
    if b % 2 = 0 then pow_mod_ (mul_mod a a) (b / 2)
    else mul_mod a (pow_mod_ (mul_mod a a) (b / 2))

let pow_mod #m a b = pow_mod_ #m a b


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


let rec lemma_pow_nat_mod_is_pow #n a b =
  let k = mk_nat_mod_comm_monoid n in
  if b = 1 then begin
    lemma_pow1 a;
    LE.lemma_pow1 k a end
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
