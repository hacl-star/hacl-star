module Hacl.Spec.Gf128.FieldPreComp

open FStar.Mul
open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

open Hacl.Spec.GF128.Vec

module GF = Spec.GaloisField
module Loops = Lib.LoopCombinators
module Lemmas = Hacl.Spec.GF128.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

type table1 = lseq uint64 128
let elem_s = lseq uint64 2

let to_elem (x:elem_s) : elem =
  mk_int #U128 (v x.[0] + v x.[1] * pow2 64)

let zero = GF.zero #gf128
let bit_mask64 (u:uint64) = u64 0 -. (u &. u64 1)


let fadd_s (x:elem_s) (y:elem_s) : elem_s =
  let r0 = x.[0] ^. y.[0] in
  let r1 = x.[1] ^. y.[1] in
  create2 r0 r1

val fadd_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (fadd_s x y) == GF.fadd (to_elem x) (to_elem y))
let fadd_lemma x y = Lemmas.logxor_s_lemma x y


let logand_s (x:elem_s) (y:elem_s) : elem_s =
  let r0 = x.[0] &. y.[0] in
  let r1 = x.[1] &. y.[1] in
  create2 r0 r1

val logand_s_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (logand_s x y) == (to_elem x &. to_elem y))
let logand_s_lemma x y = Lemmas.logand_s_lemma x y

///
///  `fmul_be_one_loop` is used to prove functional correctness of `fmul_be_s`
///

let eq_mask_get_ith_bit (x:elem_s) (i:nat{i < 128}) : uint64 =
  let (x0, x1) = (x.[0], x.[1]) in
  let x = if i < 64 then x1 >>. (63ul -. size i) else x0 >>. (127ul -. size i) in
  bit_mask64 x

let mask_logand (x:elem_s) (y:elem_s) (i:nat{i < 128}) : elem_s =
  let m = eq_mask_get_ith_bit x i in
  logand_s y (create2 m m)

let mask_add (x:elem_s) (y:elem_s) (res:elem_s) (i:nat{i < 128}): elem_s =
  fadd_s res (mask_logand x y i)

let shift_right1 (x:elem_s) : elem_s =
  let (x0, x1) = (x.[0], x.[1]) in
  create2 ((x0 >>. 1ul) |. (x1 <<. 63ul)) (x1 >>. 1ul)

let mask_shift_right_mod (y:elem_s) : elem_s =
  let irr = create2 (u64 0) (u64 0xE100000000000000) in
  fadd_s (shift_right1 y) (mask_logand y irr 127)

let fmul_be_s_f (x:elem_s) (i:nat{i < 128}) (res_y:elem_s & elem_s) : (elem_s & elem_s) =
  let (res, y) = res_y in
  let res = mask_add x y res i in
  let y = mask_shift_right_mod y in
  (res, y)

let fmul_be_one_loop (x:elem_s) (y:elem_s) : elem_s =
  let zero2 = create 2 (u64 0) in
  let (tmp, sh) = Loops.repeati 128 (fmul_be_s_f x) (zero2, y) in
  tmp


///
///  Lemma (to_elem (fmul_be_one_loop x y) == GF.fmul_be (to_elem x) (to_elem y))
///

val get_ith_bit_lemma0: x:elem_s -> i:nat{i < 64} -> Lemma
  (let (x0, x1) = (x.[0], x.[1]) in
   v ((x1 >>. (63ul -. size i)) &. u64 1) == v (GF.get_ith_bit (to_elem x) i))
let get_ith_bit_lemma0 x i =
  let (x0, x1) = (x.[0], x.[1]) in
  let lp0 = if i < 64 then x1 >>. (63ul -. size i) else x0 >>. (127ul -. size i) in
  let lp = lp0 &. u64 1 in
  logand_mask lp0 (u64 1) 1;
  assert (v lp == v lp0 % pow2 1);

  let rp = ((to_elem x) >>. size (127 - i)) &. u128 1 in
  logand_mask ((to_elem x) >>. size (127 - i)) (u128 1) 1;
  assert (v rp == (v x0 + v x1 * pow2 64) / pow2 (127 - i) % pow2 1);

  calc (==) {
    (v x0 + v x1 * pow2 64) / pow2 (127 - i) % pow2 1;
    (==) { FStar.Math.Lemmas.pow2_plus 64 (63 - i) }
    (v x0 + v x1 * pow2 64) / (pow2 64 * pow2 (63 - i)) % pow2 1;
    (==) { FStar.Math.Lemmas.division_multiplication_lemma (v x0 + v x1 * pow2 64) (pow2 64) (pow2 (63 - i)) }
    ((v x0 + v x1 * pow2 64) / pow2 64) / pow2 (63 - i) % pow2 1;
    (==) { FStar.Math.Lemmas.lemma_div_plus (v x0) (v x1) (pow2 64) }
    (v x0 / pow2 64 + v x1) / pow2 (63 - i) % pow2 1;
    (==) { FStar.Math.Lemmas.small_division_lemma_1 (v x0) (pow2 64) }
    v x1 / pow2 (63 - i) % pow2 1;
  }


val get_ith_bit_lemma1: x:elem_s -> i:nat{64 <= i /\ i < 128} -> Lemma
  (let (x0, x1) = (x.[0], x.[1]) in
   v ((x0 >>. (127ul -. size i)) &. u64 1) == v (GF.get_ith_bit (to_elem x) i))
let get_ith_bit_lemma1 x i =
  let (x0, x1) = (x.[0], x.[1]) in
  let lp0 = x0 >>. (127ul -. size i) in
  let lp = lp0 &. u64 1 in
  logand_mask lp0 (u64 1) 1;
  assert (v lp == v lp0 % pow2 1);

  let rp = ((to_elem x) >>. size (127 - i)) &. u128 1 in
  logand_mask ((to_elem x) >>. size (127 - i)) (u128 1) 1;
  assert (v rp == (v x0 + v x1 * pow2 64) / pow2 (127 - i) % pow2 1);
  let k = pow2 (i - 63) in
  let m = pow2 (127 - i) in

  calc (==) {
    (v x0 + v x1 * pow2 64) / m % pow2 1;
    (==) { FStar.Math.Lemmas.pow2_plus (i - 63) (127 - i) }
    (v x0 + v x1 * k * m) / m % pow2 1;
    (==) { FStar.Math.Lemmas.lemma_div_plus (v x0) (v x1 * k) m }
    (v x0 / m + v x1 * k) % pow2 1;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r (v x0 / m) (v x1 * k) (pow2 1)}
    (v x0 / m + v x1 * k % pow2 1) % pow2 1;
    (==) { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v x1) 1 (i - 63) }
    (v x0 / m) % pow2 1;
    }


val get_ith_bit_lemma: x:elem_s -> i:nat{i < 128} -> Lemma
  (let (x0, x1) = (x.[0], x.[1]) in
   let lp0 = if i < 64 then x1 >>. (63ul -. size i) else x0 >>. (127ul -. size i) in
   v (lp0 &. u64 1) == v (GF.get_ith_bit (to_elem x) i))
let get_ith_bit_lemma x i =
  if i < 64 then get_ith_bit_lemma0 x i
  else get_ith_bit_lemma1 x i

val eq_mask_get_ith_bit_lemma: x:elem_s -> i:nat{i < 128} -> Lemma
  (v (eq_mask_get_ith_bit x i) == v (eq_mask #U128 (GF.get_ith_bit (to_elem x) i) (u128 1)) / pow2 64 /\
   v (eq_mask_get_ith_bit x i) == v (eq_mask #U128 (GF.get_ith_bit (to_elem x) i) (u128 1)) % pow2 64)
let eq_mask_get_ith_bit_lemma x i = get_ith_bit_lemma x i
  // let (x0, x1) = (x.[0], x.[1]) in
  // let rp = eq_mask #U128 (GF.get_ith_bit (to_elem x) i) (u128 1) in
  // assert (v rp == (if v (GF.get_ith_bit (to_elem x) i) = 1 then ones_v U128 else 0));
  // let lp0 = if i < 64 then x1 >>. (63ul -. size i) else x0 >>. (127ul -. size i) in
  // get_ith_bit_lemma x i;
  // assert (v (lp0 &. u64 1) == v (GF.get_ith_bit (to_elem x) i));
  // let lp = u64 0 -. (lp0 &. u64 1) in
  // assert (v lp == (if v (lp0 &. u64 1) = 1 then ones_v U64 else 0))

val mask_logand_lemma: x:elem_s -> y:elem_s -> i:nat{i < 128} -> Lemma
  (to_elem (mask_logand x y i) == (to_elem y &. eq_mask #U128 (GF.get_ith_bit (to_elem x) i) (u128 1)))
let mask_logand_lemma x y i =
  let m = eq_mask_get_ith_bit x i in
  eq_mask_get_ith_bit_lemma x i;
  logand_s_lemma y (create2 m m)

val mask_add_lemma: x:elem_s -> y:elem_s -> res:elem_s -> i:nat{i < 128} ->
  Lemma (to_elem (mask_add x y res i) == GF.mask_add (to_elem x) (to_elem y) (to_elem res) i)
let mask_add_lemma x y res i =
  mask_logand_lemma x y i;
  fadd_lemma res (mask_logand x y i)

val shift_right1_lemma: x:elem_s -> Lemma
  (to_elem (shift_right1 x) == ((to_elem x) >>. 1ul))
let shift_right1_lemma x =
  let (x0, x1) = (x.[0], x.[1]) in
  let rp = (to_elem x) >>. 1ul in
  assert (v rp == (v x0 + v x1 * pow2 64) / pow2 1);

  let r0 = (x0 >>. 1ul) |. (x1 <<. 63ul) in
  let r1 = x1 >>. 1ul in
  calc (==) {
    v r0 + v r1 * pow2 64;
    (==) { logor_disjoint (x0 >>. 1ul) (x1 <<. 63ul) 63 }
    v x0 / pow2 1 + (v x1 * pow2 63) % pow2 64 + v x1 / pow2 1 * pow2 64;
    (==) { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v x1) 64 63 }
    v x0 / pow2 1 + (v x1 % pow2 1) * pow2 63 + v x1 / pow2 1 * pow2 64;
    (==) { assert_norm (pow2 64 = pow2 1 * pow2 63) }
    v x0 / pow2 1 + (v x1 % pow2 1) * pow2 63 + v x1 / pow2 1 * pow2 1 * pow2 63;
    (==) { FStar.Math.Lemmas.distributivity_add_left (v x1 % pow2 1) (v x1 / pow2 1) (pow2 63) }
    v x0 / pow2 1 + (v x1 % pow2 1 + v x1 / pow2 1 * pow2 1) * pow2 63;
    (==) { FStar.Math.Lemmas.euclidean_division_definition (v x1) (pow2 1)}
    v x0 / pow2 1 + v x1 * pow2 63;
    (==) { FStar.Math.Lemmas.lemma_div_plus (v x0) (v x1 * pow2 63) (pow2 1) }
    (v x0 + v x1 * pow2 64) / pow2 1;
    };
  assert (v r0 + v r1 * pow2 64 == v rp)

val mask_shift_right_mod_lemma: y:elem_s -> Lemma
  (to_elem (mask_shift_right_mod y) == GF.mask_shift_right_mod #gf128 (to_elem y))
let mask_shift_right_mod_lemma y =
  let irr = create2 (u64 0) (u64 0xE100000000000000) in
  assert_norm (to_elem irr == Spec.GF128.irred);
  shift_right1_lemma y;
  mask_logand_lemma y irr 127;
  fadd_lemma (shift_right1 y) (mask_logand y irr 127)

val fmul_be_s_f_lemma: x:elem_s -> i:nat{i < 128} -> res_y:tuple2 elem_s elem_s -> Lemma
  (let (r0, r1) = fmul_be_s_f x i res_y in let (res, y) = res_y in
   (to_elem r0, to_elem r1) == GF.fmul_be_f (to_elem x) i (to_elem res, to_elem y))
let fmul_be_s_f_lemma x i res_y =
  let (res, y) = res_y in
  mask_add_lemma x y res i;
  mask_shift_right_mod_lemma y

val fmul_be_one_loop_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (fmul_be_one_loop x y) == GF.fmul_be (to_elem x) (to_elem y))
let fmul_be_one_loop_lemma x y =
  let f = GF.fmul_be_f (to_elem x) in
  let g = fmul_be_s_f x in

  let aux_eq_f_g (i:nat{i < 128}) (res_y:tuple2 elem_s elem_s) : Lemma
    (let (res, y) = res_y in
     let (res1, y1) = g i res_y in
     f i (to_elem res, to_elem y) == (to_elem res1, to_elem y1)) =
     fmul_be_s_f_lemma x i res_y  in

  let acc_f = (u128 0, to_elem y) in
  let acc_g = (create 2 (u64 0), y) in

  let rec aux (n:nat{n <= 128}) : Lemma
    (let (res1, y1) = Loops.repeati n g acc_g in
    Loops.repeati n f acc_f == (to_elem res1, to_elem y1)) =
    if n = 0 then (
      Loops.eq_repeati0 n f acc_f;
      Loops.eq_repeati0 n g acc_g
    ) else (
      Loops.unfold_repeati n f acc_f (n-1);
      Loops.unfold_repeati n g acc_g (n-1);
      aux (n-1);
      let next_p = Loops.repeati (n-1) f acc_f in
      let next_v = Loops.repeati (n-1) g acc_g in
      aux_eq_f_g (n-1) next_v
    )
  in aux 128


///
///  Splitting the loop in `fmul_be_one_loop` into two ones to avoid branching in `eq_mask_get_ith_bit`
///


let eq_mask_get_ith_bit0 (x:uint64) (i:nat{i < 64}) : uint64 =
  bit_mask64 (x >>. (63ul -. size i))

let mask_logand0 (x:uint64) (y:elem_s) (i:nat{i < 64}) : elem_s =
  let m = eq_mask_get_ith_bit0 x i in
  logand_s y (create2 m m)

let mask_add0 (x:uint64) (y:elem_s) (res:elem_s) (i:nat{i < 64}): elem_s =
  fadd_s res (mask_logand0 x y i)

let fmul_be_s_f0 (x:uint64) (i:nat{i < 64}) (res_y:elem_s & elem_s) : (elem_s & elem_s) =
  let (res, y) = res_y in
  let res = mask_add0 x y res i in
  let y = mask_shift_right_mod y in
  (res, y)

let fmul_be_s (x:elem_s) (y:elem_s) : elem_s =
  let zero2 = create 2 (u64 0) in
  let (tmp0, sh0) = Loops.repeati 64 (fmul_be_s_f0 x.[1]) (zero2, y) in
  let (tmp, sh) = Loops.repeati 64 (fmul_be_s_f0 x.[0]) (tmp0, sh0) in
  tmp

///
///  Lemma (fmul_be_one_loop x y == fmul_be x y)
///

val fmul_be_s_eq_x0 (x:elem_s) (i:nat{i < 64}) (res_y:elem_s & elem_s) : Lemma
   (fmul_be_s_f0 x.[0] i res_y == fmul_be_s_f x (64 + i) res_y)
let fmul_be_s_eq_x0 x i res_y = ()

val fmul_be_lemma: x:elem_s -> y:elem_s -> Lemma
  (fmul_be_one_loop x y == fmul_be_s x y)
let fmul_be_lemma x y =
  let zero2 = create 2 (u64 0) in
  let f = fmul_be_s_f x in
  let g1 = fmul_be_s_f0 x.[1] in
  let g0 = fmul_be_s_f0 x.[0] in
  let a_spec = tuple2 elem_s elem_s in

  let acc_f = (zero2, y) in
  let acc_f1 = Loops.repeati 64 f acc_f in

  let res_y = Loops.repeati 128 f acc_f in
  Loops.repeati_def 128 f acc_f;
  Loops.repeat_right_plus 0 64 128 (Loops.fixed_a a_spec) f acc_f;
  Loops.repeati_def 64 f acc_f;
  assert (res_y == Loops.repeat_right 64 128 (Loops.fixed_a a_spec) f acc_f1);

  let aux_eq_f_g1 (i:nat{i < 64}) (res_y:tuple2 elem_s elem_s) : Lemma
    (g1 i res_y == f i res_y) = () in
  FStar.Classical.forall_intro_2 aux_eq_f_g1;
  Lib.Sequence.Lemmas.repeati_extensionality 64 f g1 acc_f;
  assert (Loops.repeati 64 g1 acc_f == Loops.repeati 64 f acc_f);

  Loops.repeati_def 64 g0 acc_f1;
  assert (Loops.repeati 64 g0 acc_f1 == Loops.repeat_right 0 64 (Loops.fixed_a a_spec) g0 acc_f1);

  let rec aux (n:nat{n <= 64}) : Lemma
    (Loops.repeat_right 0 n (Loops.fixed_a a_spec) g0 acc_f1 ==
     Loops.repeat_right 64 (64+n) (Loops.fixed_a a_spec) f acc_f1) =
    if n = 0 then (
      Loops.eq_repeat_right 0 n (Loops.fixed_a a_spec) g0 acc_f1;
      Loops.eq_repeat_right 64 (64+n) (Loops.fixed_a a_spec) f acc_f1
    ) else (
      Loops.unfold_repeat_right 0 n (Loops.fixed_a a_spec) g0 acc_f1 (n-1);
      Loops.unfold_repeat_right 64 (64+n) (Loops.fixed_a a_spec) f acc_f1 (64+n-1);
      aux (n-1);
      let next_p = Loops.repeat_right 0 (n-1) (Loops.fixed_a a_spec) g0 acc_f1 in
      let next_v = Loops.repeat_right 64 (64+n-1) (Loops.fixed_a a_spec) f acc_f1 in
      fmul_be_s_eq_x0 x (n-1) next_p
    )
  in aux 64;

  assert (Loops.repeat_right 64 128 (Loops.fixed_a a_spec) f acc_f1 ==
    Loops.repeat_right 0 64 (Loops.fixed_a a_spec) g0 acc_f1)


let mask_shift_right_mod_optimized (y:elem_s) : elem_s =
  let m = bit_mask64 y.[0] in
  let r0 = (y.[0] >>. 1ul) |. (y.[1] <<. 63ul) in
  let r1 = (y.[1] >>. 1ul) ^. (u64 0xE100000000000000 &. m) in
  create2 r0 r1

val mask_shift_right_mod_optimized_lemma: y:elem_s -> Lemma
  (mask_shift_right_mod y == mask_shift_right_mod_optimized y)
let mask_shift_right_mod_optimized_lemma y =
  let irr = create2 (u64 0) (u64 0xE100000000000000) in
  let m = eq_mask_get_ith_bit y 127 in
  v_injective (y.[0] >>. 0ul);
  assert (m == bit_mask64 y.[0]);
  Lib.IntTypes.logand_lemma (u64 0) m;
  logxor_lemma (shift_right1 y).[0] (u64 0)


///
///  Precomputed version of the fmul_be function
///

let precomp_s_f0 (i:nat{i < 64}) (y_pre:elem_s & table1) : elem_s & table1 =
  let (y, pre) = y_pre in
  let pre = update_sub pre (2 * i) 2 y in
  let y1 = mask_shift_right_mod y in
  y1, pre

let precomp_s0 (y:elem_s) : elem_s & table1 =
  let pre = create 128 (u64 0) in
  Loops.repeati 64 precomp_s_f0 (y, pre)

let fmul_pre_s_f0 (x:uint64) (tab:table1) (i:nat{i < 64}) (res:elem_s) : elem_s =
  mask_add0 x (sub tab (i * 2) 2) res i

let fmul_pre_s0 (x:uint64) (res0:elem_s) (y:elem_s) : elem_s & elem_s =
  let (y1, tab) = precomp_s0 y in
  let res = Loops.repeati 64 (fmul_pre_s_f0 x tab) res0 in
  (res, y1)

let fmul_pre (x:elem_s) (y:elem_s) =
  let zero2 = create 2 (u64 0) in
  let (res0, y0) = fmul_pre_s0 x.[1] zero2 y in
  let (res1, y1) = fmul_pre_s0 x.[0] res0 y0 in
  res1

///
///  Lemma (fmul_pre x y == fmul_be_one_loop x y)
///

val fmul_pre_s0_lemma: x:uint64 -> res0:elem_s -> y0:elem_s -> Lemma
  (fmul_pre_s0 x res0 y0 == Loops.repeati 64 (fmul_be_s_f0 x) (res0, y0))
let fmul_pre_s0_lemma x res0 y0 =
  let pre = create 128 (u64 0) in
  let (y1, tab) = Loops.repeati 64 precomp_s_f0 (y0, pre) in
  let res = Loops.repeati 64 (fmul_pre_s_f0 x tab) res0 in

  let rec aux (n:nat{n <= 64}) : Lemma
    (let (y1, tab) = Loops.repeati n precomp_s_f0 (y0, pre) in
     let res = Loops.repeati n (fmul_pre_s_f0 x tab) res0 in
     (res, y1) == Loops.repeati n (fmul_be_s_f0 x) (res0, y0)) =
    if n = 0 then (
      Loops.eq_repeati0 n precomp_s_f0 (y0, pre);
      let (y1, tab) = Loops.repeati n (precomp_s_f0) (y0, pre) in
      Loops.eq_repeati0 n (fmul_pre_s_f0 x tab) res0;
      Loops.eq_repeati0 n (fmul_be_s_f0 x) (res0, y0)
    ) else (
      Loops.unfold_repeati n precomp_s_f0 (y0, pre) (n-1);
      let (y1, tab) = Loops.repeati n (precomp_s_f0) (y0, pre) in
      Loops.unfold_repeati n (fmul_pre_s_f0 x tab) res0 (n-1);
      Loops.unfold_repeati n (fmul_be_s_f0 x) (res0, y0) (n-1);
      aux (n-1);

      let (y1_p, tab_p) = Loops.repeati (n-1) precomp_s_f0 (y0, pre) in
      let res_p = Loops.repeati (n-1) (fmul_pre_s_f0 x tab_p) res0 in
      let (res_v, y_v) = Loops.repeati (n-1) (fmul_be_s_f0 x) (res0, y0) in
      assert ((res_p, y1_p) == (res_v, y_v));

      let (y1_c, tab_c) = precomp_s_f0 (n-1) (y1_p, tab_p) in
      assert (Loops.repeati n precomp_s_f0 (y0, pre) == (y1_c, tab_c));
      Lib.Sequence.Lemmas.repeati_extensionality (n-1) (fmul_pre_s_f0 x tab_p) (fmul_pre_s_f0 x tab_c) res0;
      assert (Loops.repeati (n-1) (fmul_pre_s_f0 x tab_p) res0 == Loops.repeati (n-1) (fmul_pre_s_f0 x tab_c) res0);
      let res_c = fmul_pre_s_f0 x tab_c (n-1) res_p in
      assert ((res_c, y1_c) == fmul_be_s_f0 x (n-1) (res_v, y_v))
    )
  in aux 64


val fmul_pre_lemma: x:elem_s -> y:elem_s -> Lemma (fmul_pre x y == fmul_be_one_loop x y)
let fmul_pre_lemma x y =
  let zero2 = create 2 (u64 0) in
  let (res0, y0) = fmul_pre_s0 x.[1] zero2 y in
  fmul_pre_s0_lemma x.[1] zero2 y;
  fmul_pre_s0_lemma x.[0] res0 y0;
  assert (fmul_pre x y == fmul_be_s x y);
  fmul_be_lemma x y
