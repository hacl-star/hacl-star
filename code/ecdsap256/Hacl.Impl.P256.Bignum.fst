module Hacl.Impl.P256.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_v_is_as_nat: #l:BD.limb_t -> a:LSeq.lseq (BD.limb l) (v (nlimbs l)) ->
  Lemma (
    match l with
    | U64 -> 
          let (s0, s1, s2, s3) = LSeq.(a.[0], a.[1], a.[2], a.[3]) in
          BD.bn_v a == v s0 + v s1 * pow2 64 + v s2 * pow2 128 + v s3 * pow2 192
    | U32 ->
          let (s0, s1, s2, s3, s4, s5, s6, s7) =
          LSeq.(a.[0], a.[1], a.[2], a.[3], a.[4], a.[5], a.[6], a.[7]) in
          BD.bn_v a == v s0 + v s1 * pow2 32 + v s2 * pow2 64 + v s3 * pow2 96 +  v s4 * pow2 128 + v s5 * pow2 160 + v s6 * pow2 192 + v s7 * pow2 224)


let bn_v_is_as_nat #l a =
  match l with
  | U64 -> 
    let a : LSeq.lseq uint64 4 = a in
    let open Lib.Sequence in
    let open Hacl.Spec.Bignum.Definitions in
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);

    calc (==) {
      bn_v a;
    (==) { bn_eval1 (slice a 0 1); bn_eval_split_i #U64 a 1 }
      v a.[0] + pow2 64 * bn_v (slice a 1 4);
    (==) { bn_eval_split_i #U64 (slice a 1 4) 1; bn_eval1 (slice a 1 2) }
      v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * bn_v (slice a 2 4);
    (==) { bn_eval_split_i #U64 (slice a 2 4) 1; bn_eval1 (slice a 2 3) }
      v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * v a.[2]
      + pow2 64 * pow2 64 * pow2 64 * bn_v (slice a 3 4);
    (==) { bn_eval1 (slice a 3 4) }
      v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * v a.[2]
      + pow2 64 * pow2 64 * pow2 64 * v a.[3];
    }
  | U32 -> admit()


inline_for_extraction noextract
val bn_make_u64_4: res:felem U64 -> a0:uint64 -> a1:uint64 -> a2:uint64 -> a3:uint64 -> Stack unit
  (requires fun h -> live h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = v a0 + v a1 * pow2 64 + v a2 * pow2 128 + v a3 * pow2 192)

let bn_make_u64_4 res a0 a1 a2 a3 =
  let h0 = ST.get () in
  upd res 0ul a0;
  let h1 = ST.get () in
  upd res 1ul a1;
  let h2 = ST.get () in
  upd res 2ul a2;
  let h3 = ST.get () in
  upd res 3ul a3;
  let h4 = ST.get () in
  BD.bn_upd_eval (as_seq h0 res) a0 0;
  BD.bn_upd_eval (as_seq h1 res) a1 1;
  BD.bn_upd_eval (as_seq h2 res) a2 2;
  BD.bn_upd_eval (as_seq h3 res) a3 3;
  bn_v_is_as_nat (as_seq h0 res)


inline_for_extraction noextract
val bn_make_u32_8: res:felem U32 -> a0:uint32 -> a1:uint32 -> a2:uint32 -> a3:uint32 -> a4:uint32 -> a5:uint32 -> a6:uint32 -> a7:uint32 -> Stack unit
  (requires fun h -> live h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = v a0 + v a1 * pow2 32 + v a2 * pow2 64 + v a3 * pow2 96 +  v a4 * pow2 128 + v a5 * pow2 160 + v a6 * pow2 192 + v a7 * pow2 224)

let bn_make_u32_8 res a0 a1 a2 a3 a4 a5 a6 a7 =
  let h0 = ST.get () in
  upd res 0ul a0;
  let h1 = ST.get () in
  upd res 1ul a1;
  let h2 = ST.get () in
  upd res 2ul a2;
  let h3 = ST.get () in
  upd res 3ul a3;
  let h4 = ST.get () in
  upd res 4ul a4;
  let h5 = ST.get () in
  upd res 5ul a5;
  let h6 = ST.get () in
  upd res 6ul a6;
  let h7 = ST.get () in
  upd res 7ul a7;
  let h8 = ST.get () in
  BD.bn_upd_eval (as_seq h0 res) a0 0;
  BD.bn_upd_eval (as_seq h1 res) a1 1;
  BD.bn_upd_eval (as_seq h2 res) a2 2;
  BD.bn_upd_eval (as_seq h3 res) a3 3;
  BD.bn_upd_eval (as_seq h4 res) a3 4;
  BD.bn_upd_eval (as_seq h5 res) a3 5;
  BD.bn_upd_eval (as_seq h6 res) a3 6;
  BD.bn_upd_eval (as_seq h7 res) a3 3;
  bn_v_is_as_nat (as_seq h0 res);
  admit()

let felem_make_u64_4 #l res a0 a1 a2 a3 =
  admit();
  bn_make_u64_4 res a0 a1 a2 a3
  
///  Create a bignum

let create_felem l =
  BD.bn_eval_zeroes #l (v (nlimbs l)) (v (nlimbs l));
  create (nlimbs l) (limb_zero l)

let create_widefelem l =
  BD.bn_eval_zeroes #l (2 * v (nlimbs l)) (2 * v (nlimbs l));
  create (2ul *. nlimbs l) (limb_zero l)


///  Create zero and one

let felem_set_zero #l f =
  match l with
  | U64 -> bn_make_u64_4 f (u64 0) (u64 0) (u64 0) (u64 0)
  | U32 -> bn_make_u32_8 f (u32 0) (u32 0) (u32 0) (u32 0) (u32 0) (u32 0) (u32 0) (u32 0)


let felem_set_one #l f =
  match l with
  | U64 -> bn_make_u64_4 f (u64 1) (u64 0) (u64 0) (u64 0)
  | U32 -> bn_make_u32_8 f (u32 1) (u32 0) (u32 0) (u32 0) (u32 0) (u32 0) (u32 0) (u32 0)

///  Comparison

[@CInline]
let felem_is_zero_mask #l f =
  let h0 = ST.get () in
  SN.bn_is_zero_mask_lemma (as_seq h0 f);
  bn_v_is_as_nat #l (as_seq h0 f);
  BN.bn_is_zero_mask #l (nlimbs l) f


[@CInline]
let felem_is_zero_vartime f =
  let m = felem_is_zero_mask f in
  Hacl.Bignum.Base.unsafe_bool_of_limb m


[@CInline]
let felem_is_eq_mask #l a b =
  let h0 = ST.get () in
  SN.bn_eq_mask_lemma (as_seq h0 a) (as_seq h0 b);
  bn_v_is_as_nat #l (as_seq h0 a);
  bn_v_is_as_nat #l (as_seq h0 b);
  admit();
  BN.bn_eq_mask #l (nlimbs l) a b
  

[@CInline]
let felem_is_eq_vartime a b =
  let m = felem_is_eq_mask a b in
  Hacl.Bignum.Base.unsafe_bool_of_limb m


let felem_is_odd #l f =
  let h0 = ST.get () in
  bn_v_is_as_nat (as_seq h0 f);
  SN.bn_is_odd_lemma (as_seq h0 f);
  BN.bn_is_odd (nlimbs l) f


///  Conditional copy

[@CInline]
let felem_cmovznz #l res cin x y =
  let mask = neq_mask cin (limb_zero l) in
  Lib.ByteBuffer.buf_mask_select y x mask res


///  Addition and subtraction

[@CInline]
let felem_add_mod #l res n x y =
  let h0 = ST.get () in
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  BN.bn_add_mod_n (nlimbs l) n x y res


[@CInline]
let felem_sub #l res x y =
  let h0 = ST.get () in
  SN.bn_sub_lemma (as_seq h0 x) (as_seq h0 y);
  let c = BN.bn_sub_eq_len (nlimbs l) x y res in
  let h1 = ST.get () in
  assert (as_nat h1 res - v c * pow2 256 = as_nat h0 x - as_nat h0 y);
  BD.bn_eval_bound (as_seq h1 res) (v (nlimbs l));
  BD.bn_eval_bound (as_seq h0 x) (v (nlimbs l));
  BD.bn_eval_bound (as_seq h0 y) (v (nlimbs l));
  assert (if v c = 0 then as_nat h0 x >= as_nat h0 y else as_nat h0 x < as_nat h0 y);
  c


[@CInline]
let felem_sub_mod #l res n x y =
  let h0 = ST.get () in
  SN.bn_sub_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  BN.bn_sub_mod_n (nlimbs l) n x y res


///  Multiplication

[@CInline]
let felem_mul #l res x y =
  let h0 = ST.get () in
  SN.bn_mul_lemma (as_seq h0 x) (as_seq h0 y);
  BN.bn_mul #l (nlimbs l) (nlimbs l) x y res


[@CInline]
let felem_sqr #l res x =
  let h0 = ST.get () in
  SN.bn_sqr_lemma (as_seq h0 x);
  BN.bn_sqr #l (nlimbs l) x res


///  Conversion between bignum and bytes representation

[@CInline]
let felem_to_bytes_be #l res f =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma #l 32 (as_seq h0 f);
  Hacl.Bignum.Convert.mk_bn_to_bytes_be true 32ul f res


[@CInline]
let felem_from_bytes_be #l res b =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma #l 32 (as_seq h0 b);
  Hacl.Bignum.Convert.mk_bn_from_bytes_be true 32ul b res


[@CInline]
let felem2_to_bytes_be res x y =
  let h0 = ST.get () in
  update_sub_f h0 res 0ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (as_nat h0 x))
    (fun _ -> felem_to_bytes_be (sub res 0ul 32ul) x);

  let h1 = ST.get () in
  update_sub_f h1 res 32ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (as_nat h1 y))
    (fun _ -> felem_to_bytes_be (sub res 32ul 32ul) y);

  let h2 = ST.get () in
  let x = Ghost.hide (BSeq.nat_to_bytes_be 32 (as_nat h0 x)) in
  let y = Ghost.hide (BSeq.nat_to_bytes_be 32 (as_nat h0 y)) in
  LSeq.eq_intro (as_seq h2 res) (LSeq.concat #_ #32 #32 x y)
