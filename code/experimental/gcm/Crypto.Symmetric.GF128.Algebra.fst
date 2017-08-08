module Crypto.Symmetric.GF128.Algebra

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

type abelianGroup (#a: eqtype)
                  (zero: a)
		  (add: a -> a -> Tot a)
		  (opp: a -> Tot a) =
    (forall x y z. add (add x y) z = add x (add y z)) // Associativity
  /\ (forall x y. add x y = add y x)                   // Commutativity
  /\ (forall x. add x zero = x)                        // Neutral element 
  /\ (forall x. add x (opp x) = zero)                  // Inverse
  
type commutativeField (#a: eqtype)
                      (zero: a) (one: a{zero <> one})
		      (add: a -> a -> Tot a)
		      (mul: a -> a -> Tot a)
		      (opp: a -> Tot a)
		      (inv: x:a{x <> zero} -> Tot a) = 
  // '+' internal composition law
    (forall x y z. add (add x y) z = add x (add y z)) // '+' law's associativity
  /\ (forall x y. add x y = add y x)                   // '+' law's commutativity
  /\ (forall x. add x zero = x )                       // '+' neutral element
  /\ (forall x. add x (opp x) = zero)                  // inverse
  // '*' internal composition law
  /\ (forall x y z. mul (mul x y) z = mul x (mul y z)) // '*' law's associativity
  /\ (forall x y. mul x y = mul y x)                   // '*' law's commutativity
  /\ (forall x. mul x one = x)                         // '*' neutral element
  /\ (forall (x:a{x <> zero}). mul x (inv x) = one)     // inverse
  /\ (forall x y z. mul (add x y) z = add (mul x z) (mul y z)) // Distributivity

open FStar.Seq
open FStar.BitVector

(* (poly n): a polynomial over Z_2 with degree less than n. (ring Z_2[x])  *)
type poly (n:pos) = bv_t n

val expand: #m:pos -> #n:pos{m <= n} -> p:poly m ->
    Tot (p':poly n{equal p (slice p' 0 m) /\ equal (zero_vec #(n - m)) (slice p' m n)})
let expand #m #n p = append p (zero_vec #(n - m))

val part: #m:pos -> #n:pos{m >= n} -> p:poly m ->
    Tot (p':poly n{equal p' (slice p 0 n)})
let part #m #n p = slice p 0 n

val poly_add: #n:pos -> #m:pos{m <= n} -> p1:poly n -> p2:poly m -> Tot (poly n)
let poly_add #n #m p1 p2 = logxor_vec p1 (expand #m #n p2)

val poly_mul_by_scalar: #n:pos -> p:poly n -> a:bool -> Tot (poly n)
let poly_mul_by_scalar #n p a = if a then p else zero_vec #n

val poly_mul_by_xm: #n:pos -> p:poly n -> m:nat -> Tot (poly (m + n))
let poly_mul_by_xm #n p m = shift_right_vec #(m + n) (expand #n #(m + n) p) m

val poly_mul: #n:pos -> #m:pos -> p1:poly n -> p2:poly m -> Tot (poly (n + m - 1))
let rec poly_mul #n #m p1 p2 =
  if m = 1 then poly_mul_by_scalar #n p1 (index p2 0)
  else poly_add #(n + m - 1) #(n + m - 2) (poly_mul_by_xm #n (poly_mul_by_scalar #n p1 (index p2 (m - 1))) (m - 1)) (poly_mul #n #(m - 1) p1 (part #m #(m - 1) p2))

type elem = bv_t 128

val zero: elem
let zero = zero_vec #128

val add: a:elem -> b:elem -> Tot (r:elem{equal r (logxor_vec a b)})
let add x y = poly_add #128 #128 x y

val opp: elem -> Tot elem
let opp x = x

val add_commutative_lemma: unit -> Lemma 
    (requires True)
    (ensures forall x y. (add x y = add y x))
let add_commutative_lemma () = assert(forall x y. equal (add x y) (add y x))

val add_associative_lemma: unit -> Lemma
    (requires True)
    (ensures (forall x y z. add (add x y) z = add x (add y z)))
let add_associative_lemma () = assert(forall x y z. equal (add (add x y) z) (add x (add y z)))

val add_neutral_lemma: unit -> Lemma
    (requires True)
    (ensures (forall x. add x zero = x))
let add_neutral_lemma () = assert(forall (x:elem). equal x (add x zero))

val add_inverse_lemma: unit -> Lemma 
    (requires True)
    (ensures (forall x. add x (opp x) = zero))
let add_inverse_lemma () = assert(forall x. equal zero (add x (opp x)))

val test: unit -> Lemma (abelianGroup #elem zero add opp)
let test () = add_commutative_lemma(); add_associative_lemma(); add_neutral_lemma(); add_inverse_lemma()
