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
  let inp0 = (k.to.refl a, k.to.refl one) in
  Loops.eq_repeati0 bBits (S.exp_rl_f k.to.comm_monoid bBits b) inp0;

  let (a, acc) =
  Loops.repeati_inductive bBits
  (fun i (a1, acc1) ->
   (let (as, accs) = Loops.repeati i (S.exp_rl_f k.to.comm_monoid bBits b) inp0 in
    k.to.refl a1 == as /\ k.to.refl acc1 == accs))
  (fun i (a1, acc1) ->
    Loops.unfold_repeati bBits (S.exp_rl_f k.to.comm_monoid bBits b) inp0 i;
    let acc = if (b / pow2 i % 2 = 1) then k.mul acc1 a1 else acc1 in
    let a = k.mul a1 a1 in
    (a, acc)
   ) (a, one) in
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

  Loops.eq_repeati0 bBits (S.exp_mont_ladder_swap_f k.to.comm_monoid bBits b) inp0;

  let (acc, a, sw) =
  Loops.repeati_inductive bBits
  (fun i (acc1, a1, sw1) ->
   (let (accs, as, sws) = Loops.repeati i (S.exp_mont_ladder_swap_f k.to.comm_monoid bBits b) inp0 in
    k.to.refl a1 == as /\ k.to.refl acc1 == accs /\ sw1 == sws))
  (fun i (r0, r1, privbit) ->
    Loops.unfold_repeati bBits (S.exp_mont_ladder_swap_f k.to.comm_monoid bBits b) inp0 i;
    let bit = b / pow2 (bBits - i - 1) % 2 in
    let sw = (bit + privbit) % 2 in
    let r0, r1 = S.cswap sw r0 r1 in
    let r0, r1 = (k.mul r0 r0, k.mul r1 r0) in
    (r0, r1, bit)
   ) (one, a, 0) in

  let (acc, a) = S.cswap sw acc a in
  acc


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
  Loops.eq_repeat0 (S.sqr k.to.comm_monoid) (k.to.refl a);

  let acc =
  Loops.repeati_inductive b
  (fun i acc1 ->
   (let accs = Loops.repeat i (S.sqr k.to.comm_monoid) (k.to.refl a) in
    k.to.refl acc1 == accs))
  (fun i acc1 ->
    Loops.unfold_repeat b (S.sqr k.to.comm_monoid) (k.to.refl a) i;
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
  let one = k.one () in
  Loops.eq_repeati0 (bBits / l) (S.exp_fw_f k.to.comm_monoid (k.to.refl a) bBits b l) (k.to.refl one);

  let acc =
  Loops.repeati_inductive (bBits / l)
  (fun i acc1 ->
   (let accs = Loops.repeati i (S.exp_fw_f k.to.comm_monoid (k.to.refl a) bBits b l) (k.to.refl one) in
    k.to.refl acc1 == accs))
  (fun i acc1 ->
    Loops.unfold_repeati (bBits / l) (S.exp_fw_f k.to.comm_monoid (k.to.refl a) bBits b l) (k.to.refl one) i;
    let acc = exp_pow2 k acc1 l in
    let bits_l = S.get_bits_l bBits b l i in
    let acc = k.mul acc (pow k a bits_l) in
    acc
   ) one in

  assert (k.to.refl acc ==
    Loops.repeati (bBits / l) (S.exp_fw_f k.to.comm_monoid (k.to.refl a) bBits b l) (k.to.refl one));

  if bBits % l = 0 then acc
  else begin
    let c = bBits % l in
    let acc = exp_pow2 k acc c in
    let bits_c = S.get_bits_c bBits b l in
    let acc = k.mul acc (pow k a bits_c) in
    acc end
