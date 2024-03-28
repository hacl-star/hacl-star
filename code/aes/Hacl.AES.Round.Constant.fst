module Hacl.AES.Round.Constant

open FStar.Mul
open Lib.IntTypes
open Lib.LoopCombinators

open Spec.GaloisField

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val rcon_xor_2_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x00 0x02 == 0x02)

let rcon_xor_2_lemma _ =
  assert_norm (UInt.logxor #8 0x00 0x02 == 0x02)

val rcon_xor_4_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x00 0x04 == 0x04)

let rcon_xor_4_lemma _ =
  assert_norm (UInt.logxor #8 0x00 0x04 == 0x04)

val rcon_xor_8_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x00 0x08 == 0x08)

let rcon_xor_8_lemma _ =
  assert_norm (UInt.logxor #8 0x00 0x08 == 0x08)

val rcon_xor_10_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x00 0x10 == 0x10)

let rcon_xor_10_lemma _ =
  assert_norm (UInt.logxor #8 0x00 0x10 == 0x10)

val rcon_xor_20_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x00 0x20 == 0x20)

let rcon_xor_20_lemma _ =
  assert_norm (UInt.logxor #8 0x00 0x20 == 0x20)

val rcon_xor_40_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x00 0x40 == 0x40)

let rcon_xor_40_lemma _ =
  assert_norm (UInt.logxor #8 0x00 0x40 == 0x40)

val rcon_xor_80_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x00 0x80 == 0x80)

let rcon_xor_80_lemma _ =
  assert_norm (UInt.logxor #8 0x00 0x80 == 0x80)

val rcon_xor_1b_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x00 0x1b == 0x1b)

let rcon_xor_1b_lemma _ =
  assert_norm (UInt.logxor #8 0x00 0x1b == 0x1b)

val rcon_xor_36_lemma:
  (_:unit) ->
  Lemma (UInt.logxor #8 0x02 0x04 == 0x06 /\
    UInt.logxor #8 0x06 0x10 == 0x16 /\
    UInt.logxor #8 0x16 0x20 == 0x36)

let rcon_xor_36_lemma _ =
  assert_norm (UInt.logxor #8 0x02 0x04 == 0x06);
  assert_norm (UInt.logxor #8 0x06 0x10 == 0x16);
  assert_norm (UInt.logxor #8 0x16 0x20 == 0x36)

val fmul_inner_s:
  #f:field{f == gf U8 (u8 0x1b)}
  -> x:(felem f & felem f & felem f) ->
  y:(felem f & felem f & felem f){
    let (p,a,b) = x in
    let (p',a',b') = y in
    (if (v b % 2) = 1 then v p' == UInt.logxor #8 (v p) (v a)
                      else v p' == v p) /\
    (if (v a / 128) = 1 then v a' == UInt.logxor #8 ((v a * 2) % 256) 0x1b
                        else v a' == (v a * 2) % 256) /\
    v b' == v b / 2}

let fmul_inner_s #f x =
  let (p,a,b) = x in
  let one = one #f in
  let zero = zero #f in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  assert (v (b &. one) == v b % 2);
  assert (if (v b % 2) = 1 then v b0 == 0xff
                            else v b0 == 0);
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p);
  let p' = p ^. (b0 &. a) in
  assert (if (v b % 2) = 1 then v (b0 &. a) == v a
                           else v (b0 &. a) == 0);
  assert (if (v b % 2) = 1 then v p' == UInt.logxor #8 (v p) (v a)
                           else v p' == v p);
  assert_norm (pow2 7 == 128);
  let carry_mask = eq_mask #U8 (a >>. size 7) one  in
  assert (if (v a / 128) = 1 then v carry_mask == 0xff
                             else v carry_mask == 0);
  let a' = a <<. size 1 in
  assert (v a' == (v a * 2) % 256);
  logand_spec carry_mask (u8 0x1b);
  UInt.logand_commutative #8 (v carry_mask) 0x1b;
  UInt.logand_lemma_1 #8 0x1b;
  UInt.logand_lemma_2 #8 0x1b;
  logxor_spec a' (carry_mask &. u8 0x1b);
  UInt.logxor_lemma_1 #8 (v a');
  let a'' = a' ^. (carry_mask &. u8 0x1b) in
  assert (if (v a / 128) = 1 then v (carry_mask &. u8 0x1b) == 0x1b
                             else v (carry_mask &. u8 0x1b) == 0);
  assert (if (v a / 128) = 1 then v a'' == UInt.logxor #8 ((v a * 2) % 256) 0x1b
                             else v a'' == (v a * 2) % 256);
  let b' = b >>. size 1 in
  assert (v b' == v b / 2);
  (p',a'',b')

let fmul_s (#f:field{f == gf U8 (u8 0x1b)}) (a:felem f) (b:felem f) : felem f =
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let b0 = eq_mask #f.t (b &. one) one in
  let p = p ^. (b0 &. a) in
  p

val fmul_1_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x01) == u8 0x02)

let fmul_1_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x01 in
  rcon_xor_2_lemma ();
  rcon_xor_1b_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

val fmul_2_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x02) == u8 0x04)

let fmul_2_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x02 in
  rcon_xor_4_lemma ();
  rcon_xor_1b_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

val fmul_4_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x04) == u8 0x08)

let fmul_4_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x04 in
  rcon_xor_8_lemma ();
  rcon_xor_1b_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

val fmul_8_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x08) == u8 0x10)

let fmul_8_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x08 in
  rcon_xor_10_lemma ();
  rcon_xor_1b_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

val fmul_10_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x10) == u8 0x20)

let fmul_10_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x10 in
  rcon_xor_20_lemma ();
  rcon_xor_1b_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

val fmul_20_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x20) == u8 0x40)

let fmul_20_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x20 in
  rcon_xor_40_lemma ();
  rcon_xor_1b_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

val fmul_40_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x40) == u8 0x80)

let fmul_40_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x40 in
  rcon_xor_80_lemma ();
  rcon_xor_1b_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

val fmul_80_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x80) == u8 0x1b)

let fmul_80_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x80 in
  rcon_xor_1b_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

val fmul_1b_lemma:
  (_:unit) ->
  Lemma (fmul_s #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x1b) == u8 0x36)

let fmul_1b_lemma _ =
  let f = gf U8 (u8 0x1b) in
  let a = u8 0x02 in
  let b = u8 0x1b in
  rcon_xor_2_lemma ();
  rcon_xor_36_lemma ();
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) = fmul_inner_s (zero,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  let (p,a,b) = fmul_inner_s (p,a,b) in
  logand_mask b one 1;
  let b0 = eq_mask #U8 (b &. one) one in
  logand_spec b0 a;
  UInt.logand_commutative #8 (v b0) (v a);
  UInt.logand_lemma_1 #8 (v a);
  UInt.logand_lemma_2 #8 (v a);
  logxor_spec p (b0 &. a);
  UInt.logxor_lemma_1 #8 (v p)

let fmul_unroll #f (p:felem f) (a:felem f) (b:felem f) :
    Tot (felem f & felem f & felem f) =
  let (p,a,b) = fmul_inner (p,a,b) in
  let (p,a,b) = fmul_inner (p,a,b) in
  let (p,a,b) = fmul_inner (p,a,b) in
  let (p,a,b) = fmul_inner (p,a,b) in
  let (p,a,b) = fmul_inner (p,a,b) in
  let (p,a,b) = fmul_inner (p,a,b) in
  let (p,a,b) = fmul_inner (p,a,b) in
  (p,a,b)

val fmul_loop:
  #f:field{f == gf U8 (u8 0x1b)}
  -> p:felem f
  -> a:felem f
  -> b:felem f ->
  Lemma
   (fmul_unroll p a b == repeati (bits f.t - 1) (fun i -> fmul_inner) (p,a,b))

let fmul_loop #f p a b =
  eq_repeati0 (bits f.t - 1) (fun i -> fmul_inner) (p,a,b);
  unfold_repeati (bits f.t - 1) (fun i -> fmul_inner) (p,a,b) 0;
  unfold_repeati (bits f.t - 1) (fun i -> fmul_inner) (p,a,b) 1;
  unfold_repeati (bits f.t - 1) (fun i -> fmul_inner) (p,a,b) 2;
  unfold_repeati (bits f.t - 1) (fun i -> fmul_inner) (p,a,b) 3;
  unfold_repeati (bits f.t - 1) (fun i -> fmul_inner) (p,a,b) 4;
  unfold_repeati (bits f.t - 1) (fun i -> fmul_inner) (p,a,b) 5;
  unfold_repeati (bits f.t - 1) (fun i -> fmul_inner) (p,a,b) 6

val fmul_eq_lemma:
  #f:field{f == gf U8 (u8 0x1b)}
  -> a:felem f
  -> b:felem f ->
  Lemma (fmul_s a b == fmul a b)

let fmul_eq_lemma #f a b =
  fmul_loop (zero #f) a b

let fmul_lemma _ =
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x01);
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x02);
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x04);
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x08);
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x10);
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x20);
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x40);
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x80);
  fmul_eq_lemma #(gf U8 (u8 0x1b)) (u8 0x02) (u8 0x1b);
  fmul_1_lemma ();
  fmul_2_lemma ();
  fmul_4_lemma ();
  fmul_8_lemma ();
  fmul_10_lemma ();
  fmul_20_lemma ();
  fmul_40_lemma ();
  fmul_80_lemma ();
  fmul_1b_lemma ()
