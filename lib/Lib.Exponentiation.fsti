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

let sqr (#t:Type) (k:comm_monoid t) (a:t) : t = mul a a

let rec pow (#t:Type) (k:comm_monoid t) (x:t) (n:nat) : t =
  if n = 0 then one
  else mul x (pow k x (n - 1))


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
  b / pow2 (bBits - bBits % l - l * i - l) % pow2 l


let mul_acc_pow_a_bits_l (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) (acc:t) : t =
  let bits_l = get_bits_l bBits b l i in
  mul acc (pow k a bits_l)


let exp_fw_f (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) (acc:t) : t =
  let acc1 = exp_pow2 k acc l in
  mul_acc_pow_a_bits_l k a bBits b l i acc1

let exp_fw_acc0 (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) : t =
  if bBits % l = 0 then one
  else begin
    let bits_c = get_ith_lbits bBits b (bBits / l * l) l in
    pow k a bits_c end

let exp_fw (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) : t =
  let acc0 = exp_fw_acc0 k a bBits b l in
  let res = Loops.repeati (bBits / l) (exp_fw_f k a bBits b l) acc0 in
  res

val exp_fw_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos ->
  Lemma (exp_fw k a bBits b l == pow k a b)


// double exponentiation
let exp_double_fw_f (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (l:pos) (i:nat{i < bBits / l}) (acc:t) : t
 =
  let acc1 = exp_fw_f k a1 bBits b1 l i acc in
  mul_acc_pow_a_bits_l k a2 bBits b2 l i acc1


let exp_double_fw (#t:Type) (k:comm_monoid t) (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits}) (a2:t) (b2:nat{b2 < pow2 bBits}) (l:pos) : t =
  let acc_a1 = exp_fw_acc0 k a1 bBits b1 l in
  let acc_a2 = exp_fw_acc0 k a2 bBits b2 l in
  let acc0 = mul acc_a1 acc_a2 in
  let res = Loops.repeati (bBits / l) (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0 in
  res


val exp_double_fw_lemma: #t:Type -> k:comm_monoid t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos ->
  Lemma (exp_double_fw k a1 bBits b1 a2 b2 l == mul (pow k a1 b1) (pow k a2 b2))
