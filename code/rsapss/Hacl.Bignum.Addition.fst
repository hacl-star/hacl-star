module Hacl.Bignum.Addition

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Hacl.Bignum.Definitions
open Hacl.Bignum.Base
open Hacl.Impl.Lib

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = Hacl.Spec.Bignum.Addition
module LSeq = Lib.Sequence
module SL = Hacl.Spec.Lib

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val bn_sub1:
    aLen:size_t
  -> a:lbignum aLen
  -> c_in:carry
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h -> live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (let c, r = S.bn_sub1 #(v aLen) (as_seq h0 a) c_in in
    c_out == c /\ as_seq h1 res == r))

let bn_sub1 aLen a c_in res =
  push_frame ();
  let c = create 1ul c_in in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_sub1_f #(v aLen) (as_seq h a) in

  let h0 = ST.get () in
  fill_elems h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let t1 = a.(i) in
    c.(0ul) <- subborrow_u64_st c.(0ul) t1 (u64 0) (sub res i 1ul);
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1
  );
  let res = c.(0ul) in
  pop_frame ();
  res


inline_for_extraction noextract
val bn_sub_eq_len:
    aLen:size_t
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = SL.generate_elems #uint64 #carry (v aLen) (v aLen) (S.bn_sub_f (as_seq h0 a) (as_seq h0 b)) (u64 0) in
    c_out == c /\ as_seq h1 res == r))

let bn_sub_eq_len aLen a b res =
  push_frame ();
  let c = create 1ul (u64 0) in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_sub_f #(v aLen) (as_seq h a) (as_seq h b) in

  let h0 = ST.get () in
  fill_elems h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let t1 = a.(i) in
    let t2 = b.(i) in
    c.(0ul) <- subborrow_u64_st c.(0ul) t1 t2 (sub res i 1ul);
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1;
    lemma_eq_disjoint aLen aLen 1ul res b c i h0 h1
  );
  let res = c.(0ul) in
  pop_frame ();
  res


val bn_sub:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum bLen
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ eq_or_disjoint a res /\ disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_sub #(v aLen) #(v bLen) (as_seq h0 a) (as_seq h0 b) in
    c_out == c /\ as_seq h1 res == r))

[@CInline]
let bn_sub aLen a bLen b res =
  let h0 = ST.get () in
  let a0 = sub a 0ul bLen in
  let res0 = sub res 0ul bLen in
  let h1 = ST.get () in
  let c0 = bn_sub_eq_len bLen a0 b res0 in
  let h1 = ST.get () in
  if bLen <. aLen then begin
    let rLen = aLen -! bLen in
    let a1 = sub a bLen rLen in
    let res1 = sub res bLen rLen in
    let c1 = bn_sub1 rLen a1 c0 res1 in
    let h2 = ST.get () in
    LSeq.lemma_concat2 (v bLen) (as_seq h1 res0) (v rLen) (as_seq h2 res1) (as_seq h2 res);
    c1 end
  else c0



inline_for_extraction noextract
val bn_add1:
    aLen:size_t
  -> a:lbignum aLen
  -> c_in:carry
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h -> live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (let c, r = S.bn_add1 #(v aLen) (as_seq h0 a) c_in in
    c_out == c /\ as_seq h1 res == r))

let bn_add1 aLen a c_in res =
  push_frame ();
  let c = create 1ul c_in in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_add1_f #(v aLen) (as_seq h a) in

  let h0 = ST.get () in
  fill_elems h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let t1 = a.(i) in
    c.(0ul) <- addcarry_u64_st c.(0ul) t1 (u64 0) (sub res i 1ul);
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1
  );
  let res = c.(0ul) in
  pop_frame ();
  res


inline_for_extraction noextract
val bn_add_eq_len:
    aLen:size_t
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = SL.generate_elems #uint64 #carry (v aLen) (v aLen) (S.bn_add_f (as_seq h0 a) (as_seq h0 b)) (u64 0) in
    c_out == c /\ as_seq h1 res == r))

let bn_add_eq_len aLen a b res =
  push_frame ();
  let c = create 1ul (u64 0) in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_add_f #(v aLen) (as_seq h a) (as_seq h b) in

  let h0 = ST.get () in
  fill_elems h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let t1 = a.(i) in
    let t2 = b.(i) in
    c.(0ul) <- addcarry_u64_st c.(0ul) t1 t2 (sub res i 1ul);
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1;
    lemma_eq_disjoint aLen aLen 1ul res b c i h0 h1
  );
  let res = c.(0ul) in
  pop_frame ();
  res


val bn_add:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum bLen
  -> res:lbignum aLen ->
  Stack carry
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ eq_or_disjoint a res /\ disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_add #(v aLen) #(v bLen) (as_seq h0 a) (as_seq h0 b) in
    c_out == c /\ as_seq h1 res == r))

[@CInline]
let bn_add aLen a bLen b res =
  let h0 = ST.get () in
  let a0 = sub a 0ul bLen in
  let res0 = sub res 0ul bLen in
  let c0 = bn_add_eq_len bLen a0 b res0 in
  let h1 = ST.get () in
  if bLen <. aLen then begin
    let rLen = aLen -! bLen in
    let a1 = sub a bLen rLen in
    let res1 = sub res bLen rLen in
    let c1 = bn_add1 rLen a1 c0 res1 in
    let h2 = ST.get () in
    LSeq.lemma_concat2 (v bLen) (as_seq h1 res0) (v rLen) (as_seq h2 res1) (as_seq h2 res);
    c1 end
  else c0
