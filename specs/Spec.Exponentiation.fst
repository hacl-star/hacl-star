module Spec.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module S = Lib.Exponentiation
module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

val exp_rl_lemma_loop: #t:Type -> k:concrete_ops t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i <= bBits} ->
  Lemma (let one = k.one () in
    let (accs, cs) = Loops.repeati i (S.exp_rl_f k.to.comm_monoid bBits b) (k.to.refl one, k.to.refl a) in
    let (acc, c) = Loops.repeati i (exp_rl_f k bBits b) (one, a) in
    k.to.refl acc == accs /\ k.to.refl c == cs)

let rec exp_rl_lemma_loop #t k a bBits b i =
  let one = k.one () in
  let inp0 = (k.to.refl one, k.to.refl a) in
  let inp1 = (one, a) in
  let f0 = S.exp_rl_f k.to.comm_monoid bBits b in
  let f1 = exp_rl_f k bBits b in

  if i = 0 then begin
    Loops.eq_repeati0 bBits f0 inp0;
    Loops.eq_repeati0 bBits f1 inp1 end
  else begin
    exp_rl_lemma_loop #t k a bBits b (i - 1);
    Loops.unfold_repeati bBits f0 inp0 (i - 1);
    Loops.unfold_repeati bBits f1 inp1 (i - 1) end


let exp_rl_lemma #t k a bBits b =
  exp_rl_lemma_loop #t k a bBits b bBits


val exp_mont_ladder_swap_lemma_loop: #t:Type -> k:concrete_ops t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i <= bBits} ->
  Lemma (let one = k.one () in
    let (r0s, r1s, sws) =
      Loops.repeati i (S.exp_mont_ladder_swap_f k.to.comm_monoid bBits b) (k.to.refl one, k.to.refl a, 0) in
    let (r0, r1, sw) =
      Loops.repeati i (exp_mont_ladder_swap_f k bBits b) (one, a, 0) in
    k.to.refl r0 == r0s /\ k.to.refl r1 == r1s /\ sw == sws)

let rec exp_mont_ladder_swap_lemma_loop #t k a bBits b i =
  let one = k.one () in
  let inp0 = (k.to.refl one, k.to.refl a, 0) in
  let inp1 = (one, a, 0) in
  let f0 = S.exp_mont_ladder_swap_f k.to.comm_monoid bBits b in
  let f1 = exp_mont_ladder_swap_f k bBits b in

  if i = 0 then begin
    Loops.eq_repeati0 bBits f0 inp0;
    Loops.eq_repeati0 bBits f1 inp1 end
  else begin
    exp_mont_ladder_swap_lemma_loop #t k a bBits b (i - 1);
    Loops.unfold_repeati bBits f0 inp0 (i - 1);
    Loops.unfold_repeati bBits f1 inp1 (i - 1) end


let exp_mont_ladder_swap_lemma #t k a bBits b =
  exp_mont_ladder_swap_lemma_loop #t k a bBits b bBits


val exp_pow2_lemma_loop: #t:Type -> k:concrete_ops t -> a:t -> b:nat -> i:nat{i <= b} ->
  Lemma (
    let accs = Loops.repeat i (S.sqr k.to.comm_monoid) (k.to.refl a) in
    let acc = Loops.repeat i k.sqr a in
    k.to.refl acc == accs)

let rec exp_pow2_lemma_loop #t k a b i =
  if i = 0 then begin
    Loops.eq_repeat0 (S.sqr k.to.comm_monoid) (k.to.refl a);
    Loops.eq_repeat0 k.sqr a end
  else begin
    exp_pow2_lemma_loop #t k a b (i - 1);
    Loops.unfold_repeat b (S.sqr k.to.comm_monoid) (k.to.refl a) (i - 1);
    Loops.unfold_repeat b k.sqr a (i - 1) end


let exp_pow2_lemma #t k a b =
  exp_pow2_lemma_loop k a b b

#push-options "--fuel 1"
let pow_eq0 #t k a = ()

let pow_unfold #t k a i = ()

let rec pow_lemma #t k a b =
  if b = 0 then ()
  else pow_lemma k a (b - 1)
#pop-options


val exp_fw_lemma_loop: #t:Type -> k:concrete_ops t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos
  -> acc0:t -> i:nat{i <= bBits / l} ->
  Lemma (
    let acc = Loops.repeati i (exp_fw_f k a bBits b l) acc0 in
    let accs = Loops.repeati i (S.exp_fw_f k.to.comm_monoid (k.to.refl a) bBits b l) (k.to.refl acc0) in
    k.to.refl acc == accs)

let rec exp_fw_lemma_loop #t k a bBits b l acc0 i =
  let f0 = exp_fw_f k a bBits b l in
  let f1 = S.exp_fw_f k.to.comm_monoid (k.to.refl a) bBits b l in

  if i = 0 then begin
    Loops.eq_repeati0 i f0 acc0;
    Loops.eq_repeati0 i f1 (k.to.refl acc0) end
  else begin
    let acc1 = Loops.repeati (i - 1) f0 acc0 in
    let bits_l1 = S.get_bits_l bBits b l (i - 1) in
    exp_fw_lemma_loop #t k a bBits b l acc0 (i - 1);
    Loops.unfold_repeati i f0 acc0 (i - 1);
    Loops.unfold_repeati i f1 (k.to.refl acc0) (i - 1);
    exp_pow2_lemma k acc1 l;
    pow_lemma k a bits_l1 end


let exp_fw_lemma #t k a bBits b l =
  let acc0 =
    if bBits % l = 0 then one ()
    else begin
      let bits_c = S.get_ith_lbits bBits b (bBits / l * l) l in
      pow_lemma k a bits_c;
      pow k a bits_c end in

  exp_fw_lemma_loop #t k a bBits b l acc0 (bBits / l)

// Double exponentiation [a1^b1 `mul` a2^b2]
//-------------------------------------------

val exp_double_fw_lemma_loop: #t:Type -> k:concrete_ops t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos
  -> acc0:t -> i:nat{i <= bBits / l} ->
  Lemma
   (let acc = Loops.repeati i (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0 in
    let accs = Loops.repeati i
      (S.exp_double_fw_f k.to.comm_monoid (k.to.refl a1) bBits b1 (k.to.refl a2) b2 l) (k.to.refl acc0) in
    k.to.refl acc == accs)

let rec exp_double_fw_lemma_loop #t k a1 bBits b1 a2 b2 l acc0 i =
  let f0 = exp_double_fw_f k a1 bBits b1 a2 b2 l in
  let f1 = S.exp_double_fw_f k.to.comm_monoid (k.to.refl a1) bBits b1 (k.to.refl a2) b2 l in

  if i = 0 then begin
    Loops.eq_repeati0 i f0 acc0;
    Loops.eq_repeati0 i f1 (k.to.refl acc0) end
  else begin
    let acc1 = Loops.repeati (i - 1) f0 acc0 in
    let bits_l1 = S.get_bits_l bBits b1 l (i - 1) in
    let bits_l2 = S.get_bits_l bBits b2 l (i - 1) in
    exp_double_fw_lemma_loop #t k a1 bBits b1 a2 b2 l acc0 (i - 1);
    Loops.unfold_repeati i f0 acc0 (i - 1);
    Loops.unfold_repeati i f1 (k.to.refl acc0) (i - 1);
    exp_pow2_lemma k acc1 l;
    pow_lemma k a1 bits_l1;
    pow_lemma k a2 bits_l2 end


let exp_double_fw_lemma #t k a1 bBits b1 a2 b2 l =
  let acc0 =
    if bBits % l = 0 then one ()
    else begin
      let bits_c1 = S.get_ith_lbits bBits b1 (bBits / l * l) l in
      let bits_c2 = S.get_ith_lbits bBits b2 (bBits / l * l) l in
      let acc_a1 = pow k a1 bits_c1 in
      let acc_a2 = pow k a2 bits_c2 in
      pow_lemma k a1 bits_c1;
      pow_lemma k a2 bits_c2;
      k.mul acc_a1 acc_a2 end in

  exp_double_fw_lemma_loop #t k a1 bBits b1 a2 b2 l acc0 (bBits / l)

// [a1^b1 `mul` a2^b2 `mul` a3^b3 `mul` a4^b4]
//----------------------------------------------

val exp_four_fw_lemma_loop:
    #t:Type -> k:concrete_ops t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits}
  -> a3:t -> b3:nat{b3 < pow2 bBits}
  -> a4:t -> b4:nat{b4 < pow2 bBits}
  -> l:pos -> acc0:t -> i:nat{i <= bBits / l} ->
  Lemma
   (let acc = Loops.repeati i (exp_four_fw_f k a1 bBits b1 a2 b2 a3 b3 a4 b4 l) acc0 in
    let accs = Loops.repeati i
      (S.exp_four_fw_f
        k.to.comm_monoid (k.to.refl a1) bBits b1
        (k.to.refl a2) b2 (k.to.refl a3) b3 (k.to.refl a4) b4 l) (k.to.refl acc0) in
    k.to.refl acc == accs)

let rec exp_four_fw_lemma_loop #t k a1 bBits b1 a2 b2 a3 b3 a4 b4 l acc0 i =
  let f0 = exp_four_fw_f k a1 bBits b1 a2 b2 a3 b3 a4 b4 l in
  let f1 = S.exp_four_fw_f k.to.comm_monoid (k.to.refl a1) bBits b1
    (k.to.refl a2) b2 (k.to.refl a3) b3 (k.to.refl a4) b4 l in

  if i = 0 then begin
    Loops.eq_repeati0 i f0 acc0;
    Loops.eq_repeati0 i f1 (k.to.refl acc0) end
  else begin
    let acc1 = Loops.repeati (i - 1) f0 acc0 in
    let bits_l1 = S.get_bits_l bBits b1 l (i - 1) in
    let bits_l2 = S.get_bits_l bBits b2 l (i - 1) in
    let bits_l3 = S.get_bits_l bBits b3 l (i - 1) in
    let bits_l4 = S.get_bits_l bBits b4 l (i - 1) in
    exp_four_fw_lemma_loop #t k a1 bBits b1 a2 b2 a3 b3 a4 b4 l acc0 (i - 1);
    Loops.unfold_repeati i f0 acc0 (i - 1);
    Loops.unfold_repeati i f1 (k.to.refl acc0) (i - 1);
    exp_pow2_lemma k acc1 l;
    pow_lemma k a1 bits_l1;
    pow_lemma k a2 bits_l2;
    pow_lemma k a3 bits_l3;
    pow_lemma k a4 bits_l4 end


let exp_four_fw_lemma #t k a1 bBits b1 a2 b2 a3 b3 a4 b4 l =
  let acc0 =
    if bBits % l = 0 then one ()
    else begin
      let bits_c1 = S.get_ith_lbits bBits b1 (bBits / l * l) l in
      let bits_c2 = S.get_ith_lbits bBits b2 (bBits / l * l) l in
      let bits_c3 = S.get_ith_lbits bBits b3 (bBits / l * l) l in
      let bits_c4 = S.get_ith_lbits bBits b4 (bBits / l * l) l in
      let acc_a1 = pow k a1 bits_c1 in
      let acc_a2 = pow k a2 bits_c2 in
      let acc_a3 = pow k a3 bits_c3 in
      let acc_a4 = pow k a4 bits_c4 in
      pow_lemma k a1 bits_c1;
      pow_lemma k a2 bits_c2;
      pow_lemma k a3 bits_c3;
      pow_lemma k a4 bits_c4;
      let acc_a12 = k.mul acc_a1 acc_a2 in
      let acc_a34 = k.mul acc_a3 acc_a4 in
      let acc = k.mul acc_a12 acc_a34 in
      acc end in

  exp_four_fw_lemma_loop #t k a1 bBits b1 a2 b2 a3 b3 a4 b4 l acc0 (bBits / l)
