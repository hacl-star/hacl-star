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
  loop1 h0 (128ul *! nLen +! 129ul -! modBits) res spec
  (fun i ->
    Loops.unfold_repeati (128 * v nLen + 129 - v modBits) (spec h0) (as_seq h0 res) (v i);
    BN.add_mod_n n res res res
  )


inline_for_extraction noextract
val mont_reduction_f:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> j:size_t{v j < v rLen}
  -> res:lbignum (rLen +! rLen) ->
  Stack unit
  (requires fun h -> live h n /\ live h res /\ disjoint n res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.mont_reduction_f #(v nLen) #(v rLen) (as_seq h0 n) nInv_u64 (v j) (as_seq h0 res))

let mont_reduction_f nLen rLen n nInv_u64 j res =
  push_frame ();
  let qj = nInv_u64 *. res.(j) in
  // Keeping the inline_for_extraction version here.
  let c = BN.bn_mul1_lshift_add_in_place nLen n qj (rLen +! rLen) j res in
  let c = create 1ul c in

  let h0 = ST.get () in
  let res2 = sub res (j +! nLen) (rLen +! rLen -! j -! nLen) in
  let _ = update_sub_f_carry #uint64 #carry h0 res (j +! nLen) (rLen +! rLen -! j -! nLen)
    (fun h -> SB.bn_add (as_seq h0 res2) (as_seq h0 c))
    // Also keeping the inline_for_extraction version, since the nLen parameter
    // is too complicated to specialize ahead-of-time.
    (fun _ -> BN.bn_add (rLen +! rLen -! j -! nLen) res2 1ul c res2) in
  pop_frame ()


[@CInline]
let mont_reduction nLen n nInv_u64 c res =
  [@ inline_let]
  let rLen = nLen +. 1ul in
  [@ inline_let]
  let spec h = S.mont_reduction_f #(v nLen) #(v rLen) (as_seq h n) nInv_u64 in

  let h0 = ST.get () in
  loop1 h0 rLen c spec
  (fun j ->
    Loops.unfold_repeati (v rLen) (spec h0) (as_seq h0 c) (v j);
    mont_reduction_f nLen rLen n nInv_u64 j c
  );
  // Easy to specialize, but such a small function that it's not worth it (per
  // Marina's advice).
  BN.bn_rshift (rLen +! rLen) c rLen res


[@CInline]
let to_mont #nLen #_ mont_reduction n nInv_u64 r2 a aM =
  [@ inline_let]
  let rLen = nLen +. 1ul in
  push_frame ();
  let tmp = create (rLen +! rLen) (u64 0) in

  let h0 = ST.get () in
  let c = sub tmp 0ul (nLen +! nLen) in
  update_sub_f h0 tmp 0ul (nLen +! nLen)
    (fun h -> SB.bn_mul (as_seq h0 a) (as_seq h0 r2))
    (fun _ -> BN.mul a r2 c);
  mont_reduction n nInv_u64 tmp aM; // aM = c % n
  pop_frame ()


[@CInline]
let from_mont #nLen mont_reduction n nInv_u64 aM a =
  [@ inline_let]
  let rLen = nLen +. 1ul in
  push_frame ();
  let tmp = create (rLen +! rLen) (u64 0) in
  update_sub tmp 0ul rLen aM;
  let a' = create rLen (u64 0) in
  mont_reduction n nInv_u64 tmp a';
  copy a (sub a' 0ul nLen);
  pop_frame ()


[@CInline]
let mont_mul #nLen #k mont_reduction n nInv_u64 aM bM resM =
  [@ inline_let]
  let rLen = nLen +. 1ul in
  push_frame ();
  let c = create (rLen +! rLen) (u64 0) in
  // In case you need to debug the type class projection, this is the explicit
  // syntax without referring to the implicitly-defined projector.
  k.BN.mul' aM bM c; // c = aM * bM
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

inline_for_extraction noextract
let mk_runtime_mont (len: BN.meta_len): mont len = {
  bn = BN.mk_runtime_bn len;
  precomp = precomp_runtime len;
  reduction = mont_reduction_runtime len;
  to = to_runtime len;
  from = from_runtime len;
  mul = mul_runtime len;
}
