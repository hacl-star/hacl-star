module Spec.Exponentiation

open FStar.Mul

module S = Lib.Exponentiation
module Loops = Lib.LoopCombinators

inline_for_extraction
class to_comm_monoid (t:Type) = {
  a_spec: Type;
  comm_monoid: S.comm_monoid a_spec;
  refl: x:t -> a_spec;
  }


inline_for_extraction
let one_st (t:Type) (to:to_comm_monoid t) = unit ->
  Pure t
  (requires True)
  (ensures  fun one ->
    to.refl one == to.comm_monoid.S.one)


inline_for_extraction
let mul_st (t:Type) (to:to_comm_monoid t) = x:t -> y:t ->
  Pure t
  (requires True)
  (ensures  fun xy ->
    to.refl xy == to.comm_monoid.S.mul (to.refl x) (to.refl y))


inline_for_extraction
let sqr_st (t:Type) (to:to_comm_monoid t) = x:t ->
  Pure t
  (requires True)
  (ensures  fun xy ->
    to.refl xy == to.comm_monoid.S.mul (to.refl x) (to.refl x))


inline_for_extraction
class concrete_ops (t:Type) = {
  to: to_comm_monoid t;
  one: one_st t to;
  mul: mul_st t to;
  sqr: sqr_st t to;
  }


val exp_rl:
    #t:Type
  -> k:concrete_ops t
  -> a:t
  -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Pure t
  (requires True)
  (ensures  fun r ->
    k.to.refl r == S.exp_rl k.to.comm_monoid (k.to.refl a) bBits b)

let exp_rl #t k a bBits b =
  let one = k.one () in
  let inp0 = (k.to.refl one, k.to.refl a) in
  let f = S.exp_rl_f k.to.comm_monoid bBits b in
  Loops.eq_repeati0 bBits f inp0;

  let (acc, c) =
  Loops.repeati_inductive bBits
  (fun i (acc, c) ->
   (let (accs, cs) = Loops.repeati i f inp0 in
    k.to.refl acc == accs /\ k.to.refl c == cs))
  (fun i (acc, c) ->
    Loops.unfold_repeati bBits f inp0 i;
    let acc = if (S.get_ith_bit bBits b i = 0) then acc else k.mul acc c in
    let c = k.mul c c in
    (acc, c)
   ) (one, a) in
  acc


val exp_mont_ladder_swap:
    #t:Type
  -> k:concrete_ops t
  -> a:t
  -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Pure t
  (requires True)
  (ensures  fun r ->
    k.to.refl r == S.exp_mont_ladder_swap k.to.comm_monoid (k.to.refl a) bBits b)

let exp_mont_ladder_swap #t k a bBits b =
  let one = k.one () in
  let inp0 = (k.to.refl one, k.to.refl a, 0) in
  let f = S.exp_mont_ladder_swap_f k.to.comm_monoid bBits b in
  Loops.eq_repeati0 bBits f inp0;

  let (r0, r1, sw) =
  Loops.repeati_inductive bBits
  (fun i (r0, r1, sw) ->
   (let (r0s, r1s, sws) = Loops.repeati i f inp0 in
    k.to.refl r0 == r0s /\ k.to.refl r1 == r1s /\ sw == sws))
  (fun i (r0, r1, privbit) ->
    Loops.unfold_repeati bBits f inp0 i;
    let bit = S.get_ith_bit bBits b (bBits - 1 - i) in
    let sw = (bit + privbit) % 2 in
    let r0, r1 = S.cswap sw r0 r1 in
    let r0, r1 = (k.mul r0 r0, k.mul r1 r0) in
    (r0, r1, bit)
   ) (one, a, 0) in

  let (r0, r1) = S.cswap sw r0 r1 in
  r0


val exp_pow2:
    #t:Type
  -> k:concrete_ops t
  -> a:t
  -> b:nat ->
  Pure t
  (requires True)
  (ensures  fun r ->
    k.to.refl r == S.exp_pow2 k.to.comm_monoid (k.to.refl a) b)

let exp_pow2 #t k a b =
  let f = S.sqr k.to.comm_monoid in
  Loops.eq_repeat0 f (k.to.refl a);

  let acc =
  Loops.repeati_inductive b
  (fun i acc1 ->
   (let accs = Loops.repeat i f (k.to.refl a) in
    k.to.refl acc1 == accs))
  (fun i acc1 ->
    Loops.unfold_repeat b f (k.to.refl a) i;
    k.sqr acc1
   ) a in

  acc


val pow:
    #t:Type
  -> k:concrete_ops t
  -> a:t -> b:nat ->
  Pure t
  (requires True)
  (ensures  fun r ->
    k.to.refl r == S.pow k.to.comm_monoid (k.to.refl a) b)

let rec pow #t k a b =
  if b = 0 then k.one ()
  else k.mul a (pow k a (b - 1))


val exp_fw_acc0:
    #t:Type
  -> k:concrete_ops t
  -> a:t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos ->
  Pure t
  (requires True)
  (ensures  fun r ->
    k.to.refl r == S.exp_fw_acc0 k.to.comm_monoid (k.to.refl a) bBits b l)

let exp_fw_acc0 #t k a bBits b l =
  if bBits % l = 0 then k.one ()
  else begin
    let bits_c = S.get_ith_lbits bBits b (bBits / l * l) l in
    pow k a bits_c end


val exp_fw:
    #t:Type
  -> k:concrete_ops t
  -> a:t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos ->
  Pure t
  (requires True)
  (ensures  fun r ->
    k.to.refl r == S.exp_fw k.to.comm_monoid (k.to.refl a) bBits b l)

let exp_fw #t k a bBits b l =
  let acc0 = exp_fw_acc0 k a bBits b l in
  let f = S.exp_fw_f k.to.comm_monoid (k.to.refl a) bBits b l in
  Loops.eq_repeati0 (bBits / l) f (k.to.refl acc0);

  let acc =
  Loops.repeati_inductive (bBits / l)
  (fun i acc ->
   (let accs = Loops.repeati i f (k.to.refl acc0) in
    k.to.refl acc == accs))
  (fun i acc ->
    Loops.unfold_repeati (bBits / l) f (k.to.refl acc0) i;
    let acc = exp_pow2 k acc l in
    let bits_l = S.get_bits_l bBits b l i in
    let acc = k.mul acc (pow k a bits_l) in
    acc
   ) acc0 in

  assert (k.to.refl acc == Loops.repeati (bBits / l) f (k.to.refl acc0));
  acc


val exp_double_fw:
    #t:Type
  -> k:concrete_ops t
  -> a1:t
  -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits}
  -> l:pos ->
  Pure t
  (requires True)
  (ensures  fun r ->
    k.to.refl r == S.exp_double_fw k.to.comm_monoid (k.to.refl a1) bBits b1 (k.to.refl a2) b2 l)

let exp_double_fw #t k a1 bBits b1 a2 b2 l =
  let acc_a1 = exp_fw_acc0 k a1 bBits b1 l in
  let acc_a2 = exp_fw_acc0 k a2 bBits b2 l in
  let acc0 = k.mul acc_a1 acc_a2 in
  let f = S.exp_double_fw_f k.to.comm_monoid (k.to.refl a1) bBits b1 (k.to.refl a2) b2 l in
  Loops.eq_repeati0 (bBits / l) f (k.to.refl acc0);

  let acc =
  Loops.repeati_inductive (bBits / l)
  (fun i acc ->
   (let accs = Loops.repeati i f (k.to.refl acc0) in
    k.to.refl acc == accs))
  (fun i acc ->
    Loops.unfold_repeati (bBits / l) f (k.to.refl acc0) i;
    let acc = exp_pow2 k acc l in
    let bits_l1 = S.get_bits_l bBits b1 l i in
    let acc = k.mul acc (pow k a1 bits_l1) in
    let bits_l2 = S.get_bits_l bBits b2 l i in
    let acc = k.mul acc (pow k a2 bits_l2) in
    acc
   ) acc0 in

  assert (k.to.refl acc == Loops.repeati (bBits / l) f (k.to.refl acc0));
  acc
