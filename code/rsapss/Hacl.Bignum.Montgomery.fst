module Hacl.Bignum.Montgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum.Base
open Hacl.Impl.Lib

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence
module B = LowStar.Buffer

module S = Hacl.Spec.Bignum.Montgomery
module SB = Hacl.Spec.Bignum

module BN = Hacl.Bignum

friend Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let precomp_r2_mod_n #nLen #_ modBits n res =
  memset res (u64 0) nLen;
  // Note here that BN.bit_set refers to the implicitly-defined projector for
  // the type class rather than the bn_bit_set operator. So we're really
  // selecting the implementation of bn_bit_set specialized for nLen!
  BN.bit_set res (modBits -! 1ul);

  [@inline_let]
  let spec h = S.bn_lshift1_mod_n (as_seq h n) in

  let h0 = ST.get () in
  loop1 h0 (128ul *! nLen +! 1ul -! modBits) res spec
  (fun i ->
    Loops.unfold_repeati (128 * v nLen + 1 - v modBits) (spec h0) (as_seq h0 res) (v i);
    BN.add_mod_n n res res res
  )


inline_for_extraction noextract
val upd_addcarry_u64:
    len:size_t
  -> c0:carry
  -> a:uint64
  -> res:lbignum len
  -> i:size_t{v i < v len} ->
  Stack carry
  (requires fun h -> live h res)
  (ensures  fun h0 c h1 -> modifies (loc res) h0 h1 /\
   (let r = Seq.index (as_seq h0 res) (v i) in
    let (c1, r1) = addcarry_u64 c0 a r in
    c == c1 /\ as_seq h1 res == LSeq.upd (as_seq h0 res) (v i) r1))

let upd_addcarry_u64 len c0 a res i =
  let tmp = sub res i 1ul in
  let h0 = ST.get () in
  let c2 = addcarry_u64_st c0 a res.(i) (sub res i 1ul) in
  let h1 = ST.get () in
  //assert ((c2, Seq.index (as_seq h1 res) (v i)) == addcarry_u64 c0 a (Seq.index (as_seq h0 res) (v i)));
  B.modifies_buffer_elim (B.gsub #uint64 res 0ul i) (loc tmp) h0 h1;
  assert (v (i +! 1ul) + v (len -! i -! 1ul) == v len);
  B.modifies_buffer_elim (B.gsub #uint64 res (i +! 1ul) (len -! i -! 1ul)) (loc tmp) h0 h1;
  LSeq.lemma_update_sub (as_seq h0 res) (v i) 1 (LSeq.sub (as_seq h1 res) (v i) 1) (as_seq h1 res);
  //assert (as_seq h1 res == LSeq.update_sub (as_seq h0 res) (v i) 1 (LSeq.sub (as_seq h1 res) (v i) 1));
  LSeq.eq_intro (as_seq h1 res) (LSeq.upd (as_seq h0 res) (v i) (Seq.index (as_seq h1 res) (v i)));
  c2


inline_for_extraction noextract
val mont_reduction_f:
    nLen:size_t{v nLen + v nLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> j:size_t{v j < v nLen}
  -> c:lbuffer carry 1ul
  -> res:lbignum (nLen +! nLen) ->
  Stack unit
  (requires fun h ->
    live h n /\ live h res /\ live h c /\
    disjoint n res /\ disjoint n c /\ disjoint c res)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    (Seq.index (as_seq h1 c) 0, as_seq h1 res) ==
      S.mont_reduction_f #(v nLen) (as_seq h0 n) nInv_u64 (v j) (Seq.index (as_seq h0 c) 0, as_seq h0 res))

let mont_reduction_f nLen n nInv_u64 j c res =
  let qj = nInv_u64 *. res.(j) in
  // Keeping the inline_for_extraction version here.
  let c1 = BN.bn_mul1_lshift_add_in_place nLen n qj (nLen +! nLen) j res in
  c.(0ul) <- upd_addcarry_u64 (nLen +! nLen) c.(0ul) c1 res (nLen +! j)


[@CInline]
let mont_reduction nLen n nInv_u64 c res =
  push_frame ();
  let c0 = create 1ul (u64 0) in
  [@inline_let]
  let refl h i : GTot (S.mont_reduction_t i) = Seq.index (as_seq h c0) 0, as_seq h c in
  [@inline_let]
  let footprint i = loc c0 |+| loc c in
  [@ inline_let]
  let spec h = S.mont_reduction_f #(v nLen) (as_seq h n) nInv_u64 in

  let h0 = ST.get () in
  loop h0 nLen S.mont_reduction_t refl footprint spec
  (fun j ->
    Loops.unfold_repeat_gen (v nLen) S.mont_reduction_t (spec h0) (refl h0 0) (v j);
    mont_reduction_f nLen n nInv_u64 j c0 c
  );
  // Easy to specialize, but such a small function that it's not worth it (per
  // Marina's advice).
  BN.bn_rshift (nLen +! nLen) c nLen res;
  BN.bn_reduce_once nLen n c0.(0ul) res;
  pop_frame ()


[@CInline]
let to_mont #nLen #_ mont_reduction n nInv_u64 r2 a aM =
  push_frame ();
  let c = create (nLen +! nLen) (u64 0) in
  BN.mul a r2 c;
  mont_reduction n nInv_u64 c aM; // aM = c % n
  pop_frame ()


[@CInline]
let from_mont #nLen mont_reduction n nInv_u64 aM a =
  push_frame ();
  let tmp = create (nLen +! nLen) (u64 0) in
  update_sub tmp 0ul nLen aM;
  mont_reduction n nInv_u64 tmp a;
  pop_frame ()


[@CInline]
let mont_mul #nLen #k mont_reduction n nInv_u64 aM bM resM =
  push_frame ();
  let c = create (nLen +! nLen) (u64 0) in
  // In case you need to debug the type class projection, this is the explicit
  // syntax without referring to the implicitly-defined projector.
  k.BN.mul aM bM c; // c = aM * bM
  mont_reduction n nInv_u64 c resM; // resM = c % n
  pop_frame ()

[@CInline]
let mont_sqr #nLen #k mont_reduction n nInv_u64 aM resM =
  push_frame ();
  let c = create (nLen +! nLen) (u64 0) in
  k.BN.sqr aM c; // c = aM * aM
  mont_reduction n nInv_u64 c resM; // resM = c % n
  pop_frame ()

/// All of the functions above are inline_for_extraction noextract meaning that
/// they're intended to be specialized by clients for a specific value of
/// ``len``. We provide a default implementation that actually keeps ``len`` at
/// runtime, to offer a version of mod_exp where all the parameters are present
/// at run-time.

let precomp_runtime len = precomp_r2_mod_n #len #(BN.mk_runtime_bn len)
let mont_reduction_runtime len = mont_reduction len
let to_runtime len = to_mont #len #(BN.mk_runtime_bn len) (mont_reduction_runtime len)
let from_runtime len = from_mont #len (mont_reduction_runtime len)
let mul_runtime len = mont_mul #len #(BN.mk_runtime_bn len) (mont_reduction_runtime len)
let sqr_runtime len = mont_sqr #len #(BN.mk_runtime_bn len) (mont_reduction_runtime len)

inline_for_extraction noextract
let mk_runtime_mont (len: BN.meta_len): mont len = {
  bn = BN.mk_runtime_bn len;
  precomp = precomp_runtime len;
  reduction = mont_reduction_runtime len;
  to = to_runtime len;
  from = from_runtime len;
  mul = mul_runtime len;
  sqr = sqr_runtime len;
}
