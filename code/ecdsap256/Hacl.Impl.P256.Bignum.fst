module Hacl.Impl.P256.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntTypes.Intrinsics

open Hacl.Spec.P256.Felem
module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let scalar_bit #buf_type s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)


let mul64 x y result temp =
  let res = mul64_wide x y in
  let l0, h0 = to_u64 res, to_u64 (res >>. 64ul) in
  upd result (size 0) l0;
  upd temp (size 0) h0

///  Create a bignum

let bn_make_u64_4 a0 a1 a2 a3 res =
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  upd res (size 0) a0;
  upd res (size 1) a1;
  upd res (size 2) a2;
  upd res (size 3) a3


///  Create zero and one

let bn_set_zero4 f =
  bn_make_u64_4 (u64 0) (u64 0) (u64 0) (u64 0) f


let bn_set_one4 f =
  bn_make_u64_4 (u64 1) (u64 0) (u64 0) (u64 0) f


///  Comparison

[@CInline]
let bn_is_zero_mask4 f =
  let h0 = ST.get () in
  SN.bn_is_zero_mask_lemma (as_seq h0 f);
  bignum_bn_v_is_as_nat h0 f;
  BN.bn_is_zero_mask #U64 4ul f


[@CInline]
let bn_is_eq_mask4 a b =
  let h0 = ST.get () in
  SN.bn_eq_mask_lemma (as_seq h0 a) (as_seq h0 b);
  bignum_bn_v_is_as_nat h0 a;
  bignum_bn_v_is_as_nat h0 b;
  BN.bn_eq_mask #U64 4ul a b


///  Conditional copy

[@CInline]
let bn_copy_conditional4 out x mask =
  buf_mask_select x out mask out


[@CInline]
let bn_cmovznz4 cin x y out =
  let mask = neq_mask cin (u64 0) in
  buf_mask_select y x mask out


///  Addition and subtraction

[@CInline]
let bn_add4 x y out =
  let h0 = ST.get () in
  let c = BN.bn_add_eq_len 4ul x y out in
  let h1 = ST.get () in
  SN.bn_add_lemma (as_seq h0 x) (as_seq h0 y);
  bignum_bn_v_is_as_nat h0 x;
  bignum_bn_v_is_as_nat h0 y;
  bignum_bn_v_is_as_nat h1 out;
  c


[@CInline]
let bn_add8 x y out =
  let h0 = ST.get () in
  let c = BN.bn_add_eq_len 8ul x y out in
  let h1 = ST.get () in
  SN.bn_add_lemma (as_seq h0 x) (as_seq h0 y);
  bignum_bn_v_is_wide_as_nat h0 x;
  bignum_bn_v_is_wide_as_nat h0 y;
  bignum_bn_v_is_wide_as_nat h1 out;
  c


[@CInline]
let bn_add_mod4 x y n out =
  let h0 = ST.get () in
  BN.bn_add_mod_n 4ul n x y out;
  let h1 = ST.get () in
  bignum_bn_v_is_as_nat h0 n;
  bignum_bn_v_is_as_nat h0 x;
  bignum_bn_v_is_as_nat h0 y;
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  bignum_bn_v_is_as_nat h1 out


[@CInline]
let bn_sub4 x y out =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  let h0 = ST.get () in
  let c = BN.bn_sub_eq_len 4ul x y out in
  let h1 = ST.get () in
  SN.bn_sub_lemma (as_seq h0 x) (as_seq h0 y);
  bignum_bn_v_is_as_nat h0 x;
  bignum_bn_v_is_as_nat h0 y;
  bignum_bn_v_is_as_nat h1 out;
  c


[@CInline]
let bn_sub4_il x y result =
  let r0 = sub result (size 0) (size 1) in
  let r1 = sub result (size 1) (size 1) in
  let r2 = sub result (size 2) (size 1) in
  let r3 = sub result (size 3) (size 1) in

  let cc = sub_borrow_u64 (u64 0) x.(size 0) y.(size 0) r0 in
  let cc = sub_borrow_u64 cc x.(size 1) y.(size 1) r1 in
  let cc = sub_borrow_u64 cc x.(size 2) y.(size 2) r2 in
  let cc = sub_borrow_u64 cc x.(size 3) y.(size 3) r3 in

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);

  cc


[@CInline]
let bn_sub_mod4 x y n out =
  let h0 = ST.get () in
  BN.bn_sub_mod_n 4ul n x y out;
  let h1 = ST.get () in
  bignum_bn_v_is_as_nat h0 n;
  bignum_bn_v_is_as_nat h0 x;
  bignum_bn_v_is_as_nat h0 y;
  SN.bn_sub_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  bignum_bn_v_is_as_nat h1 out

///  Multiplication

[@CInline]
let bn_mul4 f r out =
  let h0 = ST.get () in
  BN.bn_mul #U64 4ul 4ul f r out;
  let h1 = ST.get () in
  SN.bn_mul_lemma (as_seq h0 f) (as_seq h0 r);
  bignum_bn_v_is_as_nat h0 f;
  bignum_bn_v_is_as_nat h0 r;
  bignum_bn_v_is_wide_as_nat h1 out


[@CInline]
let bn_sqr4 f out =
  let h0 = ST.get () in
  BN.bn_sqr #U64 4ul f out;
  let h1 = ST.get () in
  SN.bn_sqr_lemma (as_seq h0 f);
  bignum_bn_v_is_as_nat h0 f;
  bignum_bn_v_is_wide_as_nat h1 out


inline_for_extraction noextract
val mult64_0il: x: glbuffer uint64 (size 4) -> u: uint64 -> result:  lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack unit
  (requires fun h -> live h x /\ live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 ->
    let result_ = Seq.index (as_seq h1 result) 0 in
    let c = Seq.index (as_seq h1 temp) 0 in
    let f0 = Seq.index (as_seq h0 x) 0 in
    uint_v result_ + uint_v c * pow2 64 = uint_v f0 * uint_v u /\ modifies (loc result |+| loc temp) h0 h1)

let mult64_0il x u result temp =
  let f0 = index x (size 0) in
  mul64 f0 u result temp


inline_for_extraction noextract
val mult64_c: x: uint64 -> u: uint64 -> cin: uint64{uint_v cin <= 1} -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack uint64
  (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 c2 h1 -> modifies (loc result |+| loc temp) h0 h1 /\ uint_v c2 <= 1 /\ (
    let r = Seq.index (as_seq h1 result) 0 in
    let h1 = Seq.index (as_seq h1 temp) 0 in
    let h0 = Seq.index (as_seq h0 temp) 0 in
    uint_v r + uint_v c2 * pow2 64 == uint_v x * uint_v u - uint_v h1 * pow2 64 + uint_v h0 + uint_v cin))

let mult64_c x u cin result temp =
  let h = index temp (size 0) in
  mul64 x u result temp;
  let l = index result (size 0) in
  add_carry_u64 cin l h result


let mul_lemma_3 (a: nat) (c: nat) (b: nat) (d: nat) : Lemma (requires (a < c && b < d)) (ensures (a * b < c * d)) = ()

val lemma_low_level0: o0: nat -> o1: nat -> o2: nat -> o3: nat -> f0: nat  ->  f1: nat -> f2: nat ->
  f3: nat {f0 + f1 * pow2 64 + f2 * pow2 128  + f3 * pow2 192 < pow2 256} ->
  u: nat {u < pow2 64} -> h2: nat -> c1: nat -> c2: nat -> c3: nat -> h3: nat -> h4: nat ->
  Lemma
  (requires (
    h2 * pow2 64 * pow2 64 +  o0 + o1 * pow2 64 + c1 * pow2 64 * pow2 64 ==  f0 * u + f1 * u * pow2 64 /\
    o2 + c2 * pow2 64 + h3 * pow2 64 - h2 - c1  == f2 * u /\
    o3 + c3 * pow2 64 + h4 * pow2 64 - h3 - c2 == f3 * u)
  )
  (ensures
    (o0 + o1 * pow2 64 + o2 * pow2 128 +  o3 * pow2 192 + (c3 + h4) * pow2 256  == (f0  + f1 * pow2 64 + f2  * pow2 128  + f3 * pow2 192) * u /\
    f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192 < pow2 320 /\
  (c3 + h4) < pow2 64)
)


let lemma_low_level0 o0 o1 o2 o3 f0 f1 f2 f3 u h2 c1 c2 c3 h3 h4 =
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320);
  assert(h2 * pow2 64 * pow2 64 +  o0 + o1 * pow2 64 + c1 * pow2 64 * pow2 64 + o2 + c2 * pow2 64 + h3 * pow2 64 - h2 - c1 +
    o3 + c3 * pow2 64 + h4 * pow2 64 - h3 - c2 == f0 * u + f1 * u * pow2 64 + f2 * u  + f3 * u);
  assert(h2 * pow2 64 * pow2 64 +  o0 + o1 * pow2 64 + c1 * pow2 64 * pow2 64 + o2 * pow2 128 + c2 * pow2 64 * pow2 128 + h3 * pow2 64 * pow2 128 - h2 * pow2 128- c1 * pow2 128 + o3 * pow2 192 + c3 * pow2 64 * pow2 192 + h4 * pow2 64 * pow2 192 - h3 * pow2 192 - c2 * pow2 192 == f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192);
  assert(o0 + o1 * pow2 64 + o2 * pow2 128 +  o3 * pow2 192 + (c3 + h4) * pow2 256  == f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192);
  assert(f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192 == (f0 + f1 * pow2 64 + f2 * pow2 128 + f3 * pow2 192) * u);
  mul_lemma_3  (f0 + f1 * pow2 64 + f2 * pow2 128 + f3 * pow2 192) (pow2 256) u (pow2 64);
  assert((f0 + f1 * pow2 64 + f2 * pow2 128 + f3 * pow2 192) * u < pow2 320);
  assert((c3 + h4) * pow2 256 < pow2 320);
  assert(c3 + h4 < pow2 64)


inline_for_extraction noextract
val mul1_il: f:  glbuffer uint64 (size 4) -> u: uint64 -> result: lbuffer uint64 (size 4) -> Stack uint64
  (requires fun h -> live h result /\ live h f)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\
    as_nat_il h0 f * uint_v u = uint_v c * pow2 64 * pow2 64 * pow2 64 * pow2 64 + as_nat h1 result /\
    as_nat_il h0 f * uint_v u < pow2 320 /\
    uint_v c < pow2 64 - 1)


let mul1_il f u result =
  push_frame();

    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320);

  let temp = create (size 1) (u64 0) in

  let f0 = index f (size 0) in
  let f1 = index f (size 1) in
  let f2 = index f (size 2) in
  let f3 = index f (size 3) in

  let o0 = sub result (size 0) (size 1) in
  let o1 = sub result (size 1) (size 1) in
  let o2 = sub result (size 2) (size 1) in
  let o3 = sub result (size 3) (size 1) in

    let h0 = ST.get() in
  mult64_0il f u o0 temp;
    let h1 = ST.get() in
  let c1 = mult64_c f1 u (u64 0) o1 temp in
    let h2 = ST.get() in
  let c2 = mult64_c f2 u c1 o2 temp in
    let h3 = ST.get() in
  let c3 = mult64_c f3 u c2 o3 temp in
    let h4 = ST.get() in
  let temp0 = index temp (size 0) in
    lemma_low_level0 (uint_v(Seq.index (as_seq h1 o0) 0)) (uint_v (Seq.index (as_seq h2 o1) 0)) (uint_v (Seq.index (as_seq h3 o2) 0)) (uint_v (Seq.index (as_seq h4 o3) 0)) (uint_v f0) (uint_v f1) (uint_v f2) (uint_v f3) (uint_v u) (uint_v (Seq.index (as_seq h2 temp) 0)) (uint_v c1) (uint_v c2) (uint_v c3) (uint_v (Seq.index (as_seq h3 temp) 0)) (uint_v temp0);

  Hacl.Spec.P256.Lemmas.mul_lemma_4 (as_nat_il h0 f) (uint_v u) (pow2 256 - 1) (pow2 64 - 1);
  assert_norm((pow2 256 - 1) * (pow2 64 - 1) == pow2 320 - pow2 256 - pow2 64 + 1);
  assert_norm((pow2 320 - pow2 256) / pow2 256 == pow2 64 - 1);

  pop_frame();
  c3 +! temp0


[@CInline]
let bn_mul1 a b result =
  let result04 = sub result (size 0) (size 4) in
  let result48 = sub result (size 4) (size 4) in
  let c = mul1_il a b result04 in
    let h0 = ST.get() in
  upd result (size 4) c;

    assert(Lib.Sequence.index (as_seq h0 result) 5 == Lib.Sequence.index (as_seq h0 result48) 1);
    assert(Lib.Sequence.index (as_seq h0 result) 6 == Lib.Sequence.index (as_seq h0 result48) 2);
    assert(Lib.Sequence.index (as_seq h0 result) 7 == Lib.Sequence.index (as_seq h0 result48) 3);

    assert_norm( pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256)


///  pow2-operations

val lemma_shift_256: a: int -> b: int -> c: int -> d: int -> Lemma (
    a * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    b * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    c * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  +
    d * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 ==
    (a + b * pow2 64 + c * pow2 64 * pow2 64 + d * pow2 64 * pow2 64 * pow2 64) * pow2 64 * pow2 64 * pow2 64 * pow2 64)

let lemma_shift_256 a b c d = ()


[@CInline]
let bn_lshift256 i o =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);

  let h0 = ST.get() in
    upd o (size 0) (u64 0);
    upd o (size 1) (u64 0);
    upd o (size 2) (u64 0);
    upd o (size 3) (u64 0);
    upd o (size 4) i.(size 0);
    upd o (size 5) i.(size 1);
    upd o (size 6) i.(size 2);
    upd o (size 7) i.(size 3);

  lemma_shift_256
    (v (Lib.Sequence.index (as_seq h0 i) 0))
    (v (Lib.Sequence.index (as_seq h0 i) 1))
    (v (Lib.Sequence.index (as_seq h0 i) 2))
    (v (Lib.Sequence.index (as_seq h0 i) 3))


[@CInline]
let bn_rshift64 t out =
  let t1 = index t (size 1) in
  let t2 = index t (size 2) in
  let t3 = index t (size 3) in
  let t4 = index t (size 4) in
  let t5 = index t (size 5) in
  let t6 = index t (size 6) in
  let t7 = index t (size 7) in

  upd out (size 0) t1;
  upd out (size 1) t2;
  upd out (size 2) t3;
  upd out (size 3) t4;
  upd out (size 4) t5;
  upd out (size 5) t6;
  upd out (size 6) t7;
  upd out (size 7) (u64 0)


let bn_mod_pow2_64 a =
  let h0 = ST.get () in
  bignum_bn_v_is_wide_as_nat h0 a;
  Hacl.Spec.Bignum.Definitions.bn_eval_index (as_seq h0 a) 0;
  assert (v (Lib.Sequence.index (as_seq h0 a) 0) == wide_as_nat h0 a / pow2 0 % pow2 64);
  index a (size 0)


///  Conversion between bignum and bytes representation

[@CInline]
let bn_to_bytes_be4 f res =
  Lib.ByteBuffer.uints_to_bytes_be (size 4) res f


let changeEndian i =
  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 (2 * 64) * pow2 64 = pow2 (3 * 64));
  assert_norm (pow2 (3 * 64) * pow2 64 = pow2 (4 * 64));
  let zero = index i (size 0) in
  let one = index i (size 1) in
  let two = index i (size 2) in
  let three = index i (size 3) in
  upd i (size 0) three;
  upd i (size 1) two;
  upd i (size 2) one;
  upd i (size 3) zero


[@CInline]
let bn_from_bytes_be4 b res =
  Lib.ByteBuffer.uints_from_bytes_be res b;
  changeEndian res
