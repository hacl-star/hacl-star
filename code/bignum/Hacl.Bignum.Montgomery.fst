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
module BC = Hacl.Bignum.Comparison

module BN = Hacl.Bignum

friend Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let precomp_r2_mod_n_aux_st (nLen: BN.meta_len) =
    nBits:size_t{v nBits / 64 < v nLen}
  -> n:lbignum nLen
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h -> live h n /\ live h res /\ disjoint n res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.precomp_r2_mod_n_ (v nBits) (as_seq h0 n))


inline_for_extraction noextract
val precomp_r2_mod_n_:
    #nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : BN.bn nLen)
  -> precomp_r2_mod_n_aux_st nLen

let precomp_r2_mod_n_ #nLen #_ nBits n res =
  memset res (u64 0) nLen;
  // Note here that BN.bit_set refers to the implicitly-defined projector for
  // the type class rather than the bn_bit_set operator. So we're really
  // selecting the implementation of bn_bit_set specialized for nLen!
  BN.bit_set res nBits;

  [@inline_let]
  let spec h = S.bn_lshift1_mod_n (as_seq h n) in

  let h0 = ST.get () in
  loop1 h0 (128ul *! nLen -! nBits) res spec
  (fun i ->
    Loops.unfold_repeati (128 * v nLen - v nBits) (spec h0) (as_seq h0 res) (v i);
    BN.add_mod_n n res res res
  )


let precomp_r2_mod_n #nLen #_ n res =
  let h0 = ST.get () in
  let mask = BN.bn_is_zero_mask nLen n in
  SB.bn_is_zero_mask_lemma (as_seq h0 n);
  let bits =
    if FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 mask =^ 0uL) then begin
      SB.bn_get_num_bits_lemma (as_seq h0 n);
      BN.bn_get_num_bits nLen n end
    else 0ul in
  precomp_r2_mod_n_ bits n res


let new_precomp_r2_mod_n r nLen n =
  if nLen = 0ul || not (nLen <=. 0xfffffffful `FStar.UInt32.div` 128ul)
  then B.null
  else
    let h0 = ST.get () in
    let res = B.malloc r (u64 0) nLen in
    let h1 = ST.get () in
    B.(modifies_only_not_unused_in loc_none h0 h1);
    assert (B.len res == nLen);
    let res: Lib.Buffer.buffer Lib.IntTypes.uint64 = res in
    assert (B.length res == FStar.UInt32.v nLen);
    let res: lbignum nLen = res in
    precomp_r2_mod_n #nLen #(BN.mk_runtime_bn nLen) n res;
    let h2 = ST.get () in
    B.(modifies_only_not_unused_in loc_none h0 h2);
    res


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
  let h0 = ST.get () in
  c.(0ul) <- addcarry_u64_st c.(0ul) c1 res.(nLen +! j) (sub res (nLen +! j) 1ul);
  let h1 = ST.get () in
  let tmp = sub res (nLen +! j) 1ul in
  B.modifies_buffer_elim (B.gsub #uint64 res 0ul (nLen +! j)) (loc c |+| loc tmp) h0 h1;
  assert (v (nLen +! j +! 1ul) + v (nLen +! nLen -! nLen -! j -! 1ul) == v (nLen +! nLen));
  B.modifies_buffer_elim (B.gsub #uint64 res (nLen +! j +! 1ul) (nLen -! j -! 1ul)) (loc c |+| loc tmp) h0 h1;
  LSeq.lemma_update_sub (as_seq h0 res) (v nLen + v j) 1 (LSeq.sub (as_seq h1 res) (v nLen + v j) 1) (as_seq h1 res);
  LSeq.eq_intro (as_seq h1 res) (LSeq.upd (as_seq h0 res) (v nLen + v j) (Seq.index (as_seq h1 res) (v nLen + v j)))


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
