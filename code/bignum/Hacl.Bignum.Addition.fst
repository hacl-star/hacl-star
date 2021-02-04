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
val bn_sub_carry:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> c_in:carry t
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h -> live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (let c, r = S.bn_sub_carry (as_seq h0 a) c_in in
    c_out == c /\ as_seq h1 res == r))

let bn_sub_carry #t aLen a c_in res =
  push_frame ();
  let c = create 1ul c_in in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_sub_carry_f (as_seq h a) in

  let h0 = ST.get () in
  fill_elems4 h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let t1 = a.(i) in
    c.(0ul) <- subborrow_st c.(0ul) t1 (uint #t 0) (sub res i 1ul);
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1
  );
  let res = c.(0ul) in
  pop_frame ();
  res


inline_for_extraction noextract
let bn_sub_eq_len_st (t:limb_t) (aLen:size_t) =
    a:lbignum t aLen
  -> b:lbignum t aLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = SL.generate_elems (v aLen) (v aLen) (S.bn_sub_f (as_seq h0 a) (as_seq h0 b)) (uint #t 0) in
    c_out == c /\ as_seq h1 res == r))


inline_for_extraction noextract
val bn_sub_eq_len: #t:limb_t -> aLen:size_t -> bn_sub_eq_len_st t aLen
let bn_sub_eq_len #t aLen a b res =
  push_frame ();
  let c = create 1ul (uint #t 0) in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_sub_f (as_seq h a) (as_seq h b) in

  let h0 = ST.get () in
  fill_elems4 h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let t1 = a.(i) in
    let t2 = b.(i) in
    c.(0ul) <- subborrow_st c.(0ul) t1 t2 (sub res i 1ul);
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1;
    lemma_eq_disjoint aLen aLen 1ul res b c i h0 h1
  );
  let res = c.(0ul) in
  pop_frame ();
  res

[@CInline]
let bn_sub_eq_len_u32 (aLen:size_t) : bn_sub_eq_len_st U32 aLen = bn_sub_eq_len aLen
[@CInline]
let bn_sub_eq_len_u64 (aLen:size_t) : bn_sub_eq_len_st U64 aLen = bn_sub_eq_len aLen

inline_for_extraction noextract
let bn_sub_eq_len_u (#t:limb_t) (aLen:size_t) : bn_sub_eq_len_st t aLen =
  match t with
  | U32 -> bn_sub_eq_len_u32 aLen
  | U64 -> bn_sub_eq_len_u64 aLen


inline_for_extraction noextract
val bn_sub:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum t bLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ eq_or_disjoint a res /\ disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_sub (as_seq h0 a) (as_seq h0 b) in
    c_out == c /\ as_seq h1 res == r))

let bn_sub #t aLen a bLen b res =
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
    let c1 = bn_sub_carry rLen a1 c0 res1 in
    let h2 = ST.get () in
    LSeq.lemma_concat2 (v bLen) (as_seq h1 res0) (v rLen) (as_seq h2 res1) (as_seq h2 res);
    c1 end
  else c0


inline_for_extraction noextract
val bn_sub1:
    #t:limb_t
  -> aLen:size_t{0 < v aLen}
  -> a:lbignum t aLen
  -> b1:limb t
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_sub1 (as_seq h0 a) b1 in
    c_out == c /\ as_seq h1 res == r))

let bn_sub1 #t aLen a b1 res =
  let c0 = subborrow_st (uint #t 0) a.(0ul) b1 (sub res 0ul 1ul) in
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 1) (LSeq.create 1 (LSeq.index (as_seq h0 res) 0));

  if 1ul <. aLen then begin
    let rLen = aLen -! 1ul in
    let a1 = sub a 1ul rLen in
    let res1 = sub res 1ul rLen in
    let c1 = bn_sub_carry rLen a1 c0 res1 in
    let h = ST.get () in
    LSeq.lemma_concat2 1 (LSeq.sub (as_seq h0 res) 0 1) (v rLen) (as_seq h res1) (as_seq h res);
    c1 end
  else c0


inline_for_extraction noextract
val bn_add_carry:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> c_in:carry t
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h -> live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (let c, r = S.bn_add_carry (as_seq h0 a) c_in in
    c_out == c /\ as_seq h1 res == r))

let bn_add_carry #t aLen a c_in res =
  push_frame ();
  let c = create 1ul c_in in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_add_carry_f (as_seq h a) in

  let h0 = ST.get () in
  fill_elems4 h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let t1 = a.(i) in
    c.(0ul) <- addcarry_st c.(0ul) t1 (uint #t 0) (sub res i 1ul);
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1
  );
  let res = c.(0ul) in
  pop_frame ();
  res


inline_for_extraction noextract
let bn_add_eq_len_st (t:limb_t) (aLen:size_t) =
    a:lbignum t aLen
  -> b:lbignum t aLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = SL.generate_elems (v aLen) (v aLen) (S.bn_add_f (as_seq h0 a) (as_seq h0 b)) (uint #t 0) in
    c_out == c /\ as_seq h1 res == r))


inline_for_extraction noextract
val bn_add_eq_len: #t:limb_t -> aLen:size_t -> bn_add_eq_len_st t aLen
let bn_add_eq_len #t aLen a b res =
  push_frame ();
  let c = create 1ul (uint #t 0) in

  [@inline_let]
  let refl h i = LSeq.index (as_seq h c) 0 in
  [@inline_let]
  let footprint (i:size_nat{i <= v aLen}) : GTot (l:B.loc{B.loc_disjoint l (loc res) /\
    B.address_liveness_insensitive_locs `B.loc_includes` l}) = loc c in
  [@inline_let]
  let spec h = S.bn_add_f (as_seq h a) (as_seq h b) in

  let h0 = ST.get () in
  fill_elems4 h0 aLen res refl footprint spec
  (fun i ->
    let h1 = ST.get () in
    let t1 = a.(i) in
    let t2 = b.(i) in
    c.(0ul) <- addcarry_st c.(0ul) t1 t2 (sub res i 1ul);
    lemma_eq_disjoint aLen aLen 1ul res a c i h0 h1;
    lemma_eq_disjoint aLen aLen 1ul res b c i h0 h1
  );
  let res = c.(0ul) in
  pop_frame ();
  res


[@CInline]
let bn_add_eq_len_u32 (aLen:size_t) : bn_add_eq_len_st U32 aLen = bn_add_eq_len aLen
[@CInline]
let bn_add_eq_len_u64 (aLen:size_t) : bn_add_eq_len_st U64 aLen = bn_add_eq_len aLen

inline_for_extraction noextract
let bn_add_eq_len_u (#t:limb_t) (aLen:size_t) : bn_add_eq_len_st t aLen =
  match t with
  | U32 -> bn_add_eq_len_u32 aLen
  | U64 -> bn_add_eq_len_u64 aLen


inline_for_extraction noextract
val bn_add:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> bLen:size_t{v bLen <= v aLen}
  -> b:lbignum t bLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ eq_or_disjoint a res /\ disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_add (as_seq h0 a) (as_seq h0 b) in
    c_out == c /\ as_seq h1 res == r))

let bn_add #t aLen a bLen b res =
  let h0 = ST.get () in
  let a0 = sub a 0ul bLen in
  let res0 = sub res 0ul bLen in
  let c0 = bn_add_eq_len bLen a0 b res0 in
  let h1 = ST.get () in
  if bLen <. aLen then begin
    let rLen = aLen -! bLen in
    let a1 = sub a bLen rLen in
    let res1 = sub res bLen rLen in
    let c1 = bn_add_carry rLen a1 c0 res1 in
    let h2 = ST.get () in
    LSeq.lemma_concat2 (v bLen) (as_seq h1 res0) (v rLen) (as_seq h2 res1) (as_seq h2 res);
    c1 end
  else c0


inline_for_extraction noextract
val bn_add1:
    #t:limb_t
  -> aLen:size_t{0 < v aLen}
  -> a:lbignum t aLen
  -> b1:limb t
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_add1 (as_seq h0 a) b1 in
    c_out == c /\ as_seq h1 res == r))

let bn_add1 #t aLen a b1 res =
  let c0 = addcarry_st (uint #t 0) a.(0ul) b1 (sub res 0ul 1ul) in
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 1) (LSeq.create 1 (LSeq.index (as_seq h0 res) 0));

  if 1ul <. aLen then begin
    let rLen = aLen -! 1ul in
    let a1 = sub a 1ul rLen in
    let res1 = sub res 1ul rLen in
    let c1 = bn_add_carry rLen a1 c0 res1 in
    let h = ST.get () in
    LSeq.lemma_concat2 1 (LSeq.sub (as_seq h0 res) 0 1) (v rLen) (as_seq h res1) (as_seq h res);
    c1 end
  else c0
