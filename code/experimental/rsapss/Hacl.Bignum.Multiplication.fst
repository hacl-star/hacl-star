module Hacl.Bignum.Multiplication

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum
open Hacl.Bignum.Base
open Hacl.Bignum.Addition

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module B = LowStar.Buffer
module S = Hacl.Spec.Bignum.Multiplication
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val bn_mul_by_limb_addj:
    aLen:size_t
  -> a:lbignum aLen
  -> l:uint64
  -> res:lbignum aLen ->
  Stack uint64
  (requires fun h ->
    live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_mul_by_limb_addj #(v aLen) (as_seq h0 a) l (as_seq h0 res))

let bn_mul_by_limb_addj aLen a l res =
  push_frame ();
  let c = create 1ul (u64 0) in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_mul_by_limb_addj_f #(v aLen) (as_seq h a) l (as_seq h res) in

  let h0 = ST.get () in
  fill_elems h0 aLen res refl footprint spec
  (fun i ->
    c.(0ul) <- mul_carry_add_u64_st c.(0ul) a.(i) l (sub res i 1ul)
  );
  let c = c.(0ul) in
  pop_frame ();
  c


inline_for_extraction noextract
val bn_mul_:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v aLen + v bLen <= max_size_t}
  -> b:lbignum bLen
  -> j:size_t{v j < v bLen}
  -> res:lbignum (aLen +! bLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul_ #(v aLen) #(v bLen) (as_seq h0 a) (as_seq h0 b) (v j) (as_seq h0 res))

let bn_mul_ aLen a bLen b j res =
  let res' = sub res j aLen in
  let l = b.(j) in
  let h0 = ST.get () in
  let c = bn_mul_by_limb_addj aLen a l res' in
  let h1 = ST.get () in
  B.modifies_buffer_elim (B.gsub #uint64 res 0ul j) (loc res') h0 h1;
  assert (v (aLen +! bLen -! (j +! aLen)) == v aLen + v bLen - v j - v aLen);
  B.modifies_buffer_elim (B.gsub #uint64 res (j +! aLen) (aLen +! bLen -! (j +! aLen))) (loc res') h0 h1;
  LSeq.lemma_update_sub (as_seq h0 res) (v j) (v aLen) 
    (snd (S.bn_mul_by_limb_addj #(v aLen) (as_seq h0 a) l (as_seq h0 res'))) (as_seq h1 res);
  res.(aLen +! j) <- c


// bn_v h1 res == bn_v h0 a * bn_v h0 b
val bn_mul:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v aLen + v bLen <= max_size_t}
  -> b:lbignum bLen
  -> res:lbignum (aLen +! bLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul #(v aLen) #(v bLen) (as_seq h0 a) (as_seq h0 b))

[@CInline]
let bn_mul aLen a bLen b res =
  let resLen = aLen +! bLen in
  memset res (u64 0) resLen;
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 (v resLen)) (as_seq h0 res);

  [@ inline_let]
  let spec h = S.bn_mul_ (as_seq h a) (as_seq h b) in

  loop1 h0 bLen res spec
  (fun j ->
    Loops.unfold_repeati (v bLen) (spec h0) (as_seq h0 res) (v j);
    bn_mul_ aLen a bLen b j res
  )
