module Hacl.Bignum.Multiplication

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum.Base
open Hacl.Impl.Lib

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module SD = Hacl.Spec.Bignum.Definitions
module S = Hacl.Spec.Bignum.Multiplication
module SS = Hacl.Spec.Bignum.Squaring

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val bn_mul1:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> l:limb t
  -> res:lbignum t aLen ->
  Stack (limb t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_mul1 (as_seq h0 a) l)

let bn_mul1 #t aLen a l res =
  push_frame ();
  let c = create 1ul (uint #t 0) in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_mul1_f (as_seq h a) l in

  let h0 = ST.get () in
  fill_elems4 h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let a_i = a.(i) in
    let res_i = sub res i 1ul in
    c.(0ul) <- mul_wide_add_st a_i l c.(0ul) res_i;
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1
  );
  let c = c.(0ul) in
  pop_frame ();
  c


inline_for_extraction noextract
val bn_mul1_add_in_place:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> l:limb t
  -> res:lbignum t aLen ->
  Stack (limb t)
  (requires fun h ->
    live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_mul1_add_in_place (as_seq h0 a) l (as_seq h0 res))

let bn_mul1_add_in_place #t aLen a l res =
  push_frame ();
  let c = create 1ul (uint #t 0) in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_mul1_add_in_place_f (as_seq h a) l (as_seq h res) in

  let h0 = ST.get () in
  fill_elems4 h0 aLen res refl footprint spec
  (fun i ->
    let a_i = a.(i) in
    let res_i = sub res i 1ul in
    c.(0ul) <- mul_wide_add2_st a_i l c.(0ul) res_i
  );
  let c = c.(0ul) in
  pop_frame ();
  c


inline_for_extraction noextract
val bn_mul1_lshift_add:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> b_j:limb t
  -> resLen:size_t
  -> j:size_t{v j + v aLen <= v resLen}
  -> res:lbignum t resLen ->
  Stack (limb t)
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 c h1 -> modifies (loc res) h0 h1 /\
    (c, as_seq h1 res) == S.bn_mul1_lshift_add (as_seq h0 a) b_j (v j) (as_seq h0 res))

let bn_mul1_lshift_add #t aLen a b_j resLen j res =
  let res_j = sub res j aLen in
  let h0 = ST.get () in
  update_sub_f_carry h0 res j aLen
  (fun h -> S.bn_mul1_add_in_place (as_seq h0 a) b_j (as_seq h0 res_j))
  (fun _ -> bn_mul1_add_in_place aLen a b_j res_j)


inline_for_extraction noextract
let bn_mul_st (t:limb_t) =
    aLen:size_t
  -> a:lbignum t aLen
  -> bLen:size_t{0 < v bLen /\ v aLen + v bLen <= max_size_t}
  -> b:lbignum t bLen
  -> res:lbignum t (aLen +! bLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 b))

inline_for_extraction noextract
val bn_mul: #t:limb_t -> bn_mul_st t
let bn_mul #t aLen a bLen b res =
  [@inline_let]
  let resLen = aLen +! bLen in
  memset res (uint #t 0) resLen;
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 (v resLen)) (as_seq h0 res);

  let b0 = b.(0ul) in
  let c =
    update_sub_f_carry h0 res 0ul aLen
    (fun h -> S.bn_mul1 (as_seq h0 a) b0)
    (fun _ -> bn_mul1 aLen a b0 (sub res 0ul aLen)) in
  res.(aLen) <- c;

  let h1 = ST.get () in
  let inv (h:mem) (i:nat{1 <= i /\ i <= v bLen}) =
    modifies (loc res) h0 h /\
    as_seq h res == Loops.repeat_right 1 i  (Loops.fixed_a (SD.lbignum t (v resLen)))
      (S.bn_mul_ (as_seq h0 a) (as_seq h0 b)) (as_seq h1 res) in

  Loops.eq_repeat_right 1 (v bLen) (Loops.fixed_a (SD.lbignum t (v resLen)))
      (S.bn_mul_ (as_seq h0 a) (as_seq h0 b)) (as_seq h1 res);

  Lib.Loops.for 1ul bLen inv
  (fun j ->
    Loops.unfold_repeat_right 1 (v bLen) (Loops.fixed_a (SD.lbignum t (v resLen)))
      (S.bn_mul_ (as_seq h0 a) (as_seq h0 b)) (as_seq h1 res) (v j);
    let bj = b.(j) in
    res.(aLen +! j) <- bn_mul1_lshift_add aLen a bj (aLen +! bLen) j res
  );

  let h2 = ST.get () in
  assert (as_seq h2 res == S.bn_mul_unroll1 (as_seq h0 a) (as_seq h0 b));
  S.bn_mul_unroll1_is_bn_mul (as_seq h0 a) (as_seq h0 b)


[@CInline]
let bn_mul_u32 : bn_mul_st U32 = bn_mul
[@CInline]
let bn_mul_u64 : bn_mul_st U64 = bn_mul

inline_for_extraction noextract
let bn_mul_u (#t:limb_t) : bn_mul_st t =
  match t with
  | U32 -> bn_mul_u32
  | U64 -> bn_mul_u64


inline_for_extraction noextract
val bn_sqr_diag:
    #t:limb_t
  -> aLen:size_t{v aLen + v aLen <= max_size_t}
  -> a:lbignum t aLen
  -> res:lbignum t (aLen +! aLen) ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint res a /\
    as_seq h res == LSeq.create (v aLen + v aLen) (uint #t 0))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == SS.bn_sqr_diag (as_seq h0 a))

let bn_sqr_diag #t aLen a res =
  let h0 = ST.get () in

  [@inline_let]
  let spec h = SS.bn_sqr_diag_f (as_seq h a) in

  loop1 h0 aLen res spec
  (fun i ->
    Loops.unfold_repeati (v aLen) (spec h0) (as_seq h0 res) (v i);
    let (hi, lo) = mul_wide a.(i) a.(i) in
    res.(2ul *! i) <- lo;
    res.(2ul *! i +! 1ul) <- hi)


// This code is taken from BoringSSL
// https://github.com/google/boringssl/blob/master/crypto/fipsmodule/bn/mul.c#L551
inline_for_extraction noextract
let bn_sqr_st (t:limb_t) =
    aLen:size_t{0 < v aLen /\ v aLen + v aLen <= max_size_t}
  -> a:lbignum t aLen
  -> res:lbignum t (aLen +! aLen) ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == SS.bn_sqr (as_seq h0 a))

inline_for_extraction noextract
val bn_sqr: #t:limb_t -> bn_sqr_st t
let bn_sqr #t aLen a res =
  push_frame ();
  [@inline_let]
  let resLen = aLen +! aLen in
  memset res (uint #t 0) resLen;
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 (v resLen)) (as_seq h0 res);

  [@inline_let]
  let spec h = SS.bn_sqr_f (as_seq h a) in

  loop1 h0 aLen res spec
  (fun j ->
    Loops.unfold_repeati (v aLen) (spec h0) (as_seq h0 res) (v j);
    let ab = sub a 0ul j in
    let a_j = a.(j) in
    res.(j +! j) <- bn_mul1_lshift_add j ab a_j resLen j res
  );

  let c0 = Hacl.Bignum.Addition.bn_add_eq_len_u resLen res res res in
  let tmp = create resLen (uint #t 0) in
  bn_sqr_diag aLen a tmp;
  let c1 = Hacl.Bignum.Addition.bn_add_eq_len_u resLen res tmp res in
  pop_frame ()


[@CInline]
let bn_sqr_u32 : bn_sqr_st U32 = bn_sqr
[@CInline]
let bn_sqr_u64 : bn_sqr_st U64 = bn_sqr

inline_for_extraction noextract
let bn_sqr_u (#t:limb_t) : bn_sqr_st t =
  match t with
  | U32 -> bn_sqr_u32
  | U64 -> bn_sqr_u64
