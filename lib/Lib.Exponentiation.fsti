module Lib.Exponentiation

open FStar.Mul

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//we don't require to have an inverse element to be an abelian group
//so this is just commutative monoid
inline_for_extraction
class comm_monoid (t:Type) = {
  one: t;
  mul: t -> t -> t;
  lemma_one: a:t -> Lemma (mul a one == a);
  lemma_mul_assoc: a:t -> b:t -> c:t -> Lemma (mul (mul a b) c == mul a (mul b c));
  lemma_mul_comm: a:t -> b:t -> Lemma (mul a b == mul b a)
  }


inline_for_extraction
class abelian_group (t:Type) = {
  cm:comm_monoid t;
  inverse: t -> t;
  lemma_inverse: a:t -> Lemma (mul (inverse a) a == one)
  }

let sqr (#t:Type) (k:comm_monoid t) (a:t) : t = mul a a


[@(strict_on_arguments [3])]
let rec pow (#t:Type) (k:comm_monoid t) (x:t) (n:nat) : t =
  if n = 0 then one
  else mul x (pow k x (n - 1))

let pow_neg (#t:Type) (k:abelian_group t) (x:t) (n:int) : t =
  if n >= 0 then pow k.cm x n else k.inverse (pow k.cm x (- n))

// Properties of an inverse function
//---------------------------------

val lemma_inverse_one: #t:Type -> k:abelian_group t ->
  Lemma (inverse k.cm.one == k.cm.one)

val lemma_inverse_id: #t:Type -> k:abelian_group t -> a:t ->
  Lemma (inverse (inverse a) == a)

val lemma_inverse_mul: #t:Type -> k:abelian_group t -> a:t -> b:t ->
  Lemma (inverse (cm.mul a b) == cm.mul (inverse a) (inverse b))

// Properties of an exponentiation function
//--------------------------------------

val lemma_pow0: #t:Type -> k:comm_monoid t -> x:t -> Lemma (pow k x 0 == one)

val lemma_pow1: #t:Type -> k:comm_monoid t -> x:t -> Lemma (pow k x 1 == x)

val lemma_pow_unfold: #t:Type -> k:comm_monoid t -> x:t -> n:pos ->
  Lemma (mul x (pow k x (n - 1)) == pow k x n)


val lemma_pow_one: #t:Type -> k:comm_monoid t -> n:nat -> Lemma (pow k one n == one)

val lemma_pow_add: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat ->
  Lemma (mul (pow k x n) (pow k x m) == pow k x (n + m))

val lemma_pow_mul: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat ->
  Lemma (pow k (pow k x n) m == pow k x (n * m))

val lemma_pow_mul_base: #t:Type -> k:comm_monoid t -> a:t -> b:t -> n:nat ->
  Lemma (mul (pow k a n) (pow k b n) == pow k (mul a b) n)

val lemma_pow_double: #t:Type -> k:comm_monoid t -> x:t -> b:nat ->
  Lemma (pow k (mul x x) b == pow k x (b + b))


val lemma_inverse_pow: #t:Type -> k:abelian_group t -> x:t -> n:nat ->
  Lemma (inverse (pow cm x n) == pow cm (inverse x) n)

val lemma_pow_neg_one: #t:Type -> k:abelian_group t -> n:int ->
  Lemma (pow_neg k cm.one n == cm.one)

val lemma_pow_neg_add: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int ->
  Lemma (cm.mul (pow_neg k x n) (pow_neg k x m) == pow_neg k x (n + m))

val lemma_pow_neg_mul: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int ->
  Lemma (pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

val lemma_pow_neg_mul_base: #t:Type -> k:abelian_group t -> a:t -> b:t -> n:int ->
  Lemma (cm.mul (pow_neg k a n) (pow_neg k b n) == pow_neg k (cm.mul a b) n)

val lemma_pow_neg_double: #t:Type -> k:abelian_group t -> x:t -> b:int ->
  Lemma (pow_neg k (cm.mul x x) b == pow_neg k x (b + b))

//-----------------------------

let get_ith_bit (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) =
  b / pow2 i % 2

//a right-to-left binary method
let exp_rl_f (#t:Type) (k:comm_monoid t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) ((acc, c) : tuple2 t t) : tuple2 t t =
  let acc = if (get_ith_bit bBits b i = 0) then acc else mul acc c in
  let c = mul c c in
  (acc, c)

let exp_rl (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (acc, c) = Loops.repeati bBits (exp_rl_f k bBits b) (one, a) in
  acc

val exp_rl_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_rl k a bBits b == pow k a b)


//a left-to-right binary method
let exp_lr_f (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) (acc:t) : t =
  let acc = mul acc acc  in
  let acc = if (get_ith_bit bBits b (bBits - 1 - i) = 0) then acc else mul acc a in
  acc

let exp_lr (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  Loops.repeati bBits (exp_lr_f k a bBits b) one

val exp_lr_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_lr k a bBits b == pow k a b)


// Montgomery ladder for exponentiation
let exp_mont_ladder_f (#t:Type) (k:comm_monoid t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) ((r0, r1) : tuple2 t t) : tuple2 t t =
  if (get_ith_bit bBits b (bBits - 1 - i) = 0) then
    (mul r0 r0, mul r1 r0)
  else
    (mul r0 r1, mul r1 r1)

let exp_mont_ladder (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (r0, r1) = Loops.repeati bBits (exp_mont_ladder_f k bBits b) (one, a) in
  r0

val exp_mont_ladder_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder k a bBits b == pow k a b)


// Montgomery ladder for exponentiation with cswap
let cswap (#t:Type) (sw:nat) (r0:t) (r1:t) : tuple2 t t =
  if sw = 1 then (r1, r0) else (r0, r1)

// cswap -> step -> cswap -> cswap -> step -> cswap -> ..
let exp_mont_ladder_swap2_f (#t:Type) (k:comm_monoid t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) ((r0, r1) : tuple2 t t) : tuple2 t t =
  let bit = get_ith_bit bBits b (bBits - 1 - i) in
  let r0, r1 = cswap bit r0 r1 in
  let r0, r1 = (mul r0 r0, mul r1 r0) in
  let r0, r1 = cswap bit r0 r1 in
  (r0, r1)

let exp_mont_ladder_swap2 (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (r0, r1) = Loops.repeati bBits (exp_mont_ladder_swap2_f k bBits b) (one, a) in
  r0

val exp_mont_ladder_swap2_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder_swap2 k a bBits b == exp_mont_ladder k a bBits b)


// cswap -> step -> cswap -> step -> cswap -> ..
let exp_mont_ladder_swap_f (#t:Type) (k:comm_monoid t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) ((r0, r1, privbit) : tuple3 t t nat) : tuple3 t t nat =
  let bit = get_ith_bit bBits b (bBits - 1 - i) in
  let sw = (bit + privbit) % 2 in
  let r0, r1 = cswap sw r0 r1 in
  let r0, r1 = (mul r0 r0, mul r1 r0) in
  (r0, r1, bit)

let exp_mont_ladder_swap (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (r0, r1, sw) = Loops.repeati bBits (exp_mont_ladder_swap_f k bBits b) (one, a, 0) in
  let (r0, r1) = cswap sw r0 r1 in
  r0

val exp_mont_ladder_swap_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder_swap k a bBits b == exp_mont_ladder k a bBits b)


// a fixed window method
let exp_pow2 (#t:Type) (k:comm_monoid t) (a:t) (b:nat) : t =
  Loops.repeat b (sqr k) a

val exp_pow2_lemma: #t:Type -> k:comm_monoid t -> a:t -> b:nat ->
  Lemma (exp_pow2 k a b == pow k a (pow2 b))


let get_ith_lbits (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) (l:pos) =
  b / pow2 i % pow2 l

let get_bits_l (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) : r:nat{r < pow2 l} =
  Math.Lemmas.lemma_mult_le_left l (i + 1) (bBits / l);
  assert (l * (i + 1) <= l * (bBits / l));
  get_ith_lbits bBits b (bBits - bBits % l - l * i - l) l

let mul_acc_pow_a_bits_l (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) (acc:t) : t =
  let bits_l = get_bits_l bBits b l i in
  mul acc (pow k a bits_l)

let exp_fw_f (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) (acc:t) : t =
  let acc1 = exp_pow2 k acc l in
  mul_acc_pow_a_bits_l k a bBits b l i acc1


let exp_fw_acc0 (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos{bBits % l <> 0}) : t =
  let bits_c = get_ith_lbits bBits b (bBits / l * l) l in
  pow k a bits_c

let exp_fw (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) : t =
  let acc0 = if bBits % l = 0 then one else exp_fw_acc0 k a bBits b l in
  let res = Loops.repeati (bBits / l) (exp_fw_f k a bBits b l) acc0 in
  res

val exp_fw_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos ->
  Lemma (exp_fw k a bBits b l == pow k a b)


///  Multi-Exponentiation

// Double exponentiation [a1^b1 `mul` a2^b2]
//-------------------------------------------

let exp_double_fw_f (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (l:pos) (i:nat{i < bBits / l}) (acc:t) : t
 =
  let acc1 = exp_fw_f k a2 bBits b2 l i acc in
  mul_acc_pow_a_bits_l k a1 bBits b1 l i acc1

let exp_double_fw_acc0 (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits}) (l:pos{bBits % l <> 0}) : t =
  let acc_a1 = exp_fw_acc0 k a1 bBits b1 l in
  let acc_a2 = exp_fw_acc0 k a2 bBits b2 l in
  mul acc_a1 acc_a2

let exp_double_fw (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits}) (l:pos) : t =
  let acc0 = if bBits % l = 0 then one else exp_double_fw_acc0 k a1 bBits b1 a2 b2 l in
  Loops.repeati (bBits / l) (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0

val exp_double_fw_lemma: #t:Type -> k:comm_monoid t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos ->
  Lemma (exp_double_fw k a1 bBits b1 a2 b2 l == mul (pow k a1 b1) (pow k a2 b2))


// [a1^b1 `mul` a2^b2 `mul` a3^b3 `mul` a4^b4]
//----------------------------------------------

let exp_four_fw_f (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (a3:t) (b3:nat{b3 < pow2 bBits})
  (a4:t) (b4:nat{b4 < pow2 bBits})
  (l:pos) (i:nat{i < bBits / l}) (acc:t) : t
 =
  let acc = exp_fw_f k a4 bBits b4 l i acc in
  let acc = mul_acc_pow_a_bits_l k a3 bBits b3 l i acc in
  let acc = mul_acc_pow_a_bits_l k a2 bBits b2 l i acc in
  let acc = mul_acc_pow_a_bits_l k a1 bBits b1 l i acc in
  acc

let exp_four_fw_acc0 (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (a3:t) (b3:nat{b3 < pow2 bBits})
  (a4:t) (b4:nat{b4 < pow2 bBits})
  (l:pos{bBits % l <> 0}) : t =
  let acc_a12 = exp_double_fw_acc0 k a1 bBits b1 a2 b2 l in
  let acc_a34 = exp_double_fw_acc0 k a3 bBits b3 a4 b4 l in
  mul acc_a12 acc_a34

let exp_four_fw (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (a3:t) (b3:nat{b3 < pow2 bBits})
  (a4:t) (b4:nat{b4 < pow2 bBits})
  (l:pos) : t =
  let acc0 =
    if bBits % l = 0 then one
    else exp_four_fw_acc0 k a1 bBits b1 a2 b2 a3 b3 a4 b4 l in
  Loops.repeati (bBits / l)
    (exp_four_fw_f k a1 bBits b1 a2 b2 a3 b3 a4 b4 l) acc0

val exp_four_fw_lemma: #t:Type -> k:comm_monoid t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits}
  -> a3:t -> b3:nat{b3 < pow2 bBits}
  -> a4:t -> b4:nat{b4 < pow2 bBits}
  -> l:pos ->
  Lemma (exp_four_fw k a1 bBits b1 a2 b2 a3 b3 a4 b4 l ==
    mul (mul (mul (pow k a1 b1) (pow k a2 b2)) (pow k a3 b3)) (pow k a4 b4))
