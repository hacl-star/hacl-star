module Hacl.Bignum.Montgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum.Base

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence
module B = LowStar.Buffer

module S = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Bignum

friend Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_check_modulus #t #len n =
  push_frame ();
  let one = create len (uint #t 0) in
  BN.bn_from_uint len (uint #t 1) one;
  let bit0 = BN.bn_is_odd len n in
  let m0 = uint #t 0 -. bit0 in
  let m1 = BN.bn_lt_mask len one n in
  let m = m0 &. m1 in
  pop_frame ();
  m


let bn_precomp_r2_mod_n #t k nBits n res =
  [@inline_let] let len = k.BN.len in
  memset res (uint #t 0) len;
  BN.bn_set_ith_bit len res nBits;

  [@inline_let]
  let spec h = S.bn_lshift1_mod_n (as_seq h n) in

  let h0 = ST.get () in
  loop1 h0 (2ul *! size (bits t) *! len -! nBits) res spec
  (fun i ->
    Loops.unfold_repeati (2 * bits t * v len - v nBits) (spec h0) (as_seq h0 res) (v i);
    BN.add_mod_n n res res res
  )


let bn_mont_precomp #t len precompr2 nBits n r2 =
  precompr2 nBits n r2;
  mod_inv_limb n.(0ul)


inline_for_extraction noextract
val bn_mont_reduction_f:
    #t:limb_t
  -> len:size_t{v len + v len <= max_size_t}
  -> n:lbignum t len
  -> nInv:(limb t)
  -> j:size_t{v j < v len}
  -> c:lbuffer (carry t) 1ul
  -> res:lbignum t (len +! len) ->
  Stack unit
  (requires fun h ->
    live h n /\ live h res /\ live h c /\
    disjoint n res /\ disjoint n c /\ disjoint c res)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    (Seq.index (as_seq h1 c) 0, as_seq h1 res) ==
      S.bn_mont_reduction_f (as_seq h0 n) nInv (v j) (Seq.index (as_seq h0 c) 0, as_seq h0 res))

let bn_mont_reduction_f #t len n nInv j c res =
  let qj = nInv *. res.(j) in
  // Keeping the inline_for_extraction version here.
  let c1 = BN.bn_mul1_lshift_add_in_place len n qj (len +! len) j res in
  let h0 = ST.get () in
  let resb = sub res (len +! j) 1ul in
  let res_j = res.(len +! j) in
  c.(0ul) <- addcarry_st c.(0ul) c1 res_j resb;
  let h1 = ST.get () in
  let tmp = sub res (len +! j) 1ul in
  B.modifies_buffer_elim (B.gsub #(limb t) res 0ul (len +! j)) (loc c |+| loc tmp) h0 h1;
  assert (v (len +! j +! 1ul) + v (len +! len -! len -! j -! 1ul) == v (len +! len));
  B.modifies_buffer_elim (B.gsub #(limb t) res (len +! j +! 1ul) (len -! j -! 1ul)) (loc c |+| loc tmp) h0 h1;
  LSeq.lemma_update_sub (as_seq h0 res) (v len + v j) 1 (LSeq.sub (as_seq h1 res) (v len + v j) 1) (as_seq h1 res);
  LSeq.eq_intro (as_seq h1 res) (LSeq.upd (as_seq h0 res) (v len + v j) (Seq.index (as_seq h1 res) (v len + v j)))


inline_for_extraction noextract
let bn_mont_reduction_loop_div_r_st (t:limb_t) (len:size_t{0 < v len /\ v len + v len <= max_size_t}) =
    n:lbignum t len
  -> mu:limb t
  -> c:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack (carry t)
  (requires fun h ->
    live h n /\ live h c /\ live h res /\
    disjoint res n /\ disjoint res c /\ disjoint n c)
  (ensures  fun h0 c0 h1 -> modifies (loc res |+| loc c) h0 h1 /\
    (c0, as_seq h1 res) == S.bn_mont_reduction_loop_div_r (as_seq h0 n) mu (as_seq h0 c))


inline_for_extraction noextract
val bn_mont_reduction_loop_div_r: #t:limb_t -> k:BN.bn t -> bn_mont_reduction_loop_div_r_st t k.BN.len
let bn_mont_reduction_loop_div_r #t k n nInv c res =
  [@inline_let] let len = k.BN.len in
  push_frame ();
  let c0 = create 1ul (uint #t 0) in
  [@inline_let]
  let refl h i : GTot (S.bn_mont_reduction_t i) = Seq.index (as_seq h c0) 0, as_seq h c in
  [@inline_let]
  let footprint i = loc c0 |+| loc c in
  [@ inline_let]
  let spec h = S.bn_mont_reduction_f (as_seq h n) nInv in

  let h0 = ST.get () in
  loop h0 len S.bn_mont_reduction_t refl footprint spec
  (fun j ->
    Loops.unfold_repeat_gen (v len) S.bn_mont_reduction_t (spec h0) (refl h0 0) (v j);
    bn_mont_reduction_f len n nInv j c0 c
  );
  BN.bn_rshift (len +! len) c len res;
  let c0 = c0.(0ul) in
  pop_frame ();
  c0


let bn_mont_reduction #t k n nInv c res =
  [@inline_let] let len = k.BN.len in
  let c0 = bn_mont_reduction_loop_div_r #t k n nInv c res in
  BN.bn_reduce_once len n c0 res


let bn_to_mont #t k mont_reduction n nInv r2 a aM =
  [@inline_let] let len = k.BN.len in
  push_frame ();
  let c = create (len +! len) (uint #t 0) in
  BN.mul a r2 c;
  mont_reduction n nInv c aM;
  pop_frame ()


let bn_from_mont #t k mont_reduction n nInv_u64 aM a =
  [@inline_let] let len = k.BN.len in
  push_frame ();
  let tmp = create (len +! len) (uint #t 0) in
  update_sub tmp 0ul len aM;
  mont_reduction n nInv_u64 tmp a;
  pop_frame ()


let bn_mont_mul #t k mont_reduction n nInv_u64 aM bM resM =
  [@inline_let] let len = k.BN.len in
  push_frame ();
  let c = create (len +! len) (uint #t 0) in
  // In case you need to debug the type class projection, this is the explicit
  // syntax without referring to the implicitly-defined projector.
  k.BN.mul aM bM c;
  mont_reduction n nInv_u64 c resM;
  pop_frame ()


let bn_mont_sqr #t k mont_reduction n nInv_u64 aM resM =
  [@inline_let] let len = k.BN.len in
  push_frame ();
  let c = create (len +! len) (uint #t 0) in
  k.BN.sqr aM c;
  mont_reduction n nInv_u64 c resM;
  pop_frame ()


/// All of the functions above are inline_for_extraction noextract meaning that
/// they're intended to be specialized by clients for a specific value of
/// ``len``. We provide a default implementation that actually keeps ``len`` at
/// runtime, to offer a version of mod_exp where all the parameters are present
/// at run-time.
let bn_check_modulus_u32 (len:BN.meta_len U32) : bn_check_modulus_st U32 len =
  bn_check_modulus #U32 #len
let bn_precomp_r2_mod_n_u32 (len:BN.meta_len U32) : bn_precomp_r2_mod_n_st U32 len =
  bn_precomp_r2_mod_n (BN.mk_runtime_bn U32 len)
let bn_mont_reduction_u32 (len:BN.meta_len U32) : bn_mont_reduction_st U32 len =
  bn_mont_reduction (BN.mk_runtime_bn U32 len)
let bn_to_mont_u32 (len:BN.meta_len U32) : bn_to_mont_st U32 len =
  bn_to_mont (BN.mk_runtime_bn U32 len) (bn_mont_reduction_u32 len)
let bn_from_mont_u32 (len:BN.meta_len U32) : bn_from_mont_st U32 len =
  bn_from_mont (BN.mk_runtime_bn U32 len) (bn_mont_reduction_u32 len)
let bn_mont_mul_u32 (len:BN.meta_len U32) : bn_mont_mul_st U32 len =
  bn_mont_mul (BN.mk_runtime_bn U32 len) (bn_mont_reduction_u32 len)
let bn_mont_sqr_u32 (len:BN.meta_len U32) : bn_mont_sqr_st U32 len =
  bn_mont_sqr (BN.mk_runtime_bn U32 len) (bn_mont_reduction_u32 len)

inline_for_extraction noextract
let mk_runtime_mont_u32 (len:BN.meta_len U32) : mont U32 = {
  bn = BN.mk_runtime_bn U32 len;
  mont_check = bn_check_modulus_u32 len;
  precomp = bn_precomp_r2_mod_n_u32 len;
  reduction = bn_mont_reduction_u32 len;
  to = bn_to_mont_u32 len;
  from = bn_from_mont_u32 len;
  mul = bn_mont_mul_u32 len;
  sqr = bn_mont_sqr_u32 len;
}


let bn_check_modulus_u64 (len:BN.meta_len U64) : bn_check_modulus_st U64 len =
  bn_check_modulus #U64 #len
let bn_precomp_r2_mod_n_u64 (len:BN.meta_len U64) : bn_precomp_r2_mod_n_st U64 len =
  bn_precomp_r2_mod_n (BN.mk_runtime_bn U64 len)
let bn_mont_reduction_u64 (len:BN.meta_len U64) : bn_mont_reduction_st U64 len =
  bn_mont_reduction (BN.mk_runtime_bn U64 len)
let bn_to_mont_u64 (len:BN.meta_len U64) : bn_to_mont_st U64 len =
  bn_to_mont (BN.mk_runtime_bn U64 len) (bn_mont_reduction_u64 len)
let bn_from_mont_u64 (len:BN.meta_len U64) : bn_from_mont_st U64 len =
  bn_from_mont (BN.mk_runtime_bn U64 len) (bn_mont_reduction_u64 len)
let bn_mont_mul_u64 (len:BN.meta_len U64) : bn_mont_mul_st U64 len =
  bn_mont_mul (BN.mk_runtime_bn U64 len) (bn_mont_reduction_u64 len)
let bn_mont_sqr_u64 (len:BN.meta_len U64) : bn_mont_sqr_st U64 len =
  bn_mont_sqr (BN.mk_runtime_bn U64 len) (bn_mont_reduction_u64 len)

inline_for_extraction noextract
let mk_runtime_mont_u64 (len:BN.meta_len U64) : mont U64 = {
  bn = BN.mk_runtime_bn U64 len;
  mont_check = bn_check_modulus_u64 len;
  precomp = bn_precomp_r2_mod_n_u64 len;
  reduction = bn_mont_reduction_u64 len;
  to = bn_to_mont_u64 len;
  from = bn_from_mont_u64 len;
  mul = bn_mont_mul_u64 len;
  sqr = bn_mont_sqr_u64 len;
}

let mk_runtime_mont (#t:limb_t) (len:BN.meta_len t) : mont t =
  match t with
  | U32 -> mk_runtime_mont_u32 len
  | U64 -> mk_runtime_mont_u64 len

let mk_runtime_mont_len_lemma #t len = ()


let bn_mont_one #t len bn_from_mont n mu r2 oneM =
  bn_from_mont n mu r2 oneM
