module Hacl.Bignum.PrecompTable

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators
module B = LowStar.Buffer

module S = Hacl.Spec.Bignum.PrecompTable
module SN = Hacl.Spec.Bignum
module SM = Hacl.Spec.Bignum.Montgomery
module BB = Hacl.Spec.Bignum.Base

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mod_precomp_table_mont_f_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> i:size_t{v i < v table_len - 2}
  -> table:lbignum t (table_len *! len) ->
  Stack unit
  (requires fun h ->
    live h n /\ live h aM /\ live h table /\
    disjoint table aM /\ disjoint table n /\ disjoint n aM)
  (ensures  fun h0 _ h1 -> modifies (loc table) h0 h1 /\
    as_seq h1 table == S.bn_mod_precomp_table_mont_f (as_seq h0 n) mu
      (as_seq h0 aM) (v table_len) (v i) (as_seq h0 table))


inline_for_extraction noextract
val bn_mod_precomp_table_mont_f: #t:limb_t -> k:BM.mont t -> bn_mod_precomp_table_mont_f_st t k.BM.bn.BN.len
let bn_mod_precomp_table_mont_f #t k n mu aM table_len i table =
  [@inline_let] let len : BN.meta_len t = k.BM.bn.BN.len in
  Math.Lemmas.lemma_mult_le_right (v len) (v i + 3) (v table_len);
  let t1 = sub table ((i +! 1ul) *! len) len in
  let t2 = sub table ((i +! 2ul) *! len) len in
  let h0 = ST.get () in
  [@ inline_let]
  let spec h0 = SM.bn_mont_mul (as_seq h0 n) mu (as_seq h0 t1) (as_seq h0 aM) in

  update_sub_f h0 table ((i +! 2ul) *! len) len spec
    (fun _ -> k.BM.mul n mu t1 aM t2);
  let h1 = ST.get () in
  assert (as_seq h1 table == LSeq.update_sub (as_seq h0 table) ((v i + 2) * v len) (v len) (spec h0))



inline_for_extraction noextract
let bn_mod_precomp_table_mont_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> aM:lbignum t len
  -> oneM:lbignum t len
  -> table:lbignum t (table_len *! len) ->
  Stack unit
  (requires fun h ->
    live h n /\ live h aM /\ live h oneM /\ live h table /\
    disjoint table oneM /\ disjoint table aM /\ disjoint table n /\
    disjoint n aM /\ disjoint n oneM /\
    as_seq h table == LSeq.create (v table_len * v len) (uint #t 0))
  (ensures  fun h0 _ h1 -> modifies (loc table) h0 h1 /\
    as_seq h1 table == S.bn_mod_precomp_table_mont (as_seq h0 n) mu (v table_len) (as_seq h0 aM) (as_seq h0 oneM))


inline_for_extraction noextract
val bn_mod_precomp_table_mont: #t:limb_t -> k:BM.mont t -> bn_mod_precomp_table_mont_st t k.BM.bn.BN.len
let bn_mod_precomp_table_mont #t k n mu table_len aM oneM table =
  [@inline_let] let len : BN.meta_len t = k.BM.bn.BN.len in
  update_sub table 0ul len oneM;
  update_sub table len len aM;

  let h0 = ST.get () in
  [@ inline_let]
  let spec h = S.bn_mod_precomp_table_mont_f (as_seq h0 n) mu (as_seq h0 aM) (v table_len) in
  loop1 h0 (table_len -! 2ul) table spec
  (fun j ->
    Loops.unfold_repeati (v table_len - 2) (spec h0) (as_seq h0 table) (v j);
    bn_mod_precomp_table_mont_f #t k n mu aM table_len j table
  )


inline_for_extraction noextract
let table_select_ct_f_st (t:limb_t) (len:BN.meta_len t) =
    table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:lbignum t (table_len *! len)
  -> i:limb t{v i < v table_len}
  -> j:size_t{v j < v table_len - 1}
  -> acc:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h table /\ live h acc /\ disjoint acc table)
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    as_seq h1 acc == S.table_select_ct_f (v table_len) (as_seq h0 table) i (v j) (as_seq h0 acc))


inline_for_extraction noextract
val table_select_ct_f: #t:limb_t -> len:BN.meta_len t -> table_select_ct_f_st t len
let table_select_ct_f #t len table_len table i j acc =
  let c = eq_mask i (BB.size_to_limb (j +! 1ul)) in
  Math.Lemmas.lemma_mult_le_right (v len) (v j + 2) (v table_len);
  assert (v ((j +! 1ul) *! len) == (v j + 1) * v len);
  let res_j = sub table ((j +! 1ul) *! len) len in
  map2T len acc (BB.mask_select c) res_j acc


inline_for_extraction noextract
let table_select_ct_st (t:limb_t) (len:BN.meta_len t) =
    table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:lbignum t (table_len *! len)
  -> i:limb t{v i < v table_len /\ (v i + 1) * v len <= v table_len * v len}
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h table /\ live h res /\ disjoint table res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.table_select_ct (v table_len) (as_seq h0 table) i /\
    as_seq h1 res == LSeq.sub (as_seq h0 table) (v i * v len) (v len))


inline_for_extraction noextract
val table_select_ct: #t:limb_t -> len:BN.meta_len t -> table_select_ct_st t len
let table_select_ct #t len table_len table i res =
  copy res (sub table 0ul len);

  [@inline_let]
  let spec h0 = S.table_select_ct_f #t #(v len) (v table_len) (as_seq h0 table) i in

  let h0 = ST.get () in
  loop1 h0 (table_len -! 1ul) res spec
  (fun j ->
    Loops.unfold_repeati (v table_len - 1) (spec h0) (as_seq h0 res) (v j);
    table_select_ct_f len table_len table i j res
  );
  let h1 = ST.get () in
  assert (as_seq h1 res == S.table_select_ct (v table_len) (as_seq h0 table) i);
  S.table_select_ct_lemma #t #(v len) (v table_len) (as_seq h0 table) i
