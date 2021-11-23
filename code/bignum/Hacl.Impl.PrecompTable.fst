module Hacl.Impl.PrecompTable

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module BB = Hacl.Bignum.Base
module PT = Hacl.Spec.PrecompTable

open Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val table_select_consttime_f:
    #t:limb_t
  -> len:size_t{v len > 0}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:lbuffer (uint_t t SEC) (table_len *! len)
  -> i:uint_t t SEC{v i < v table_len}
  -> j:size_t{v j < v table_len - 1}
  -> acc:lbuffer (uint_t t SEC) len ->
  Stack unit
  (requires fun h ->
    live h table /\ live h acc /\ disjoint table acc)
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    as_seq h1 acc ==
    PT.table_select_f (v len) (v table_len) (as_seq h0 table) i (v j) (as_seq h0 acc))

let table_select_consttime_f #t len table_len table i j acc =
  let c = eq_mask i (BB.size_to_limb (j +! 1ul)) in

  Math.Lemmas.lemma_mult_le_right (v len) (v j + 2) (v table_len);
  assert (v ((j +! 1ul) *! len) == (v j + 1) * v len);
  let res_j = sub table ((j +! 1ul) *! len) len in
  map2T len acc (BB.mask_select c) res_j acc


inline_for_extraction noextract
val table_select_consttime:
    #t:limb_t
  -> len:size_t{v len > 0}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:lbuffer (uint_t t SEC) (table_len *! len)
  -> i:uint_t t SEC{v i < v table_len}
  -> res:lbuffer (uint_t t SEC) len ->
  Stack unit
  (requires fun h ->
    (v i + 1) * v len <= v table_len * v len /\
    live h table /\ live h res /\ disjoint table res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == LSeq.sub (as_seq h0 table) (v i * v len) (v len))

let table_select_consttime #t len table_len table i res =
  let h0 = ST.get () in
  copy res (sub table 0ul len);

  let h1 = ST.get () in
  assert (as_seq h1 res == LSeq.sub (as_seq h0 table) 0 (v len));

  [@ inline_let]
  let inv h (j:nat{j <= v table_len - 1}) =
    modifies (loc res) h0 h /\
    as_seq h res ==
    Loops.repeati j
      (PT.table_select_f (v len) (v table_len) (as_seq h0 table) i) (as_seq h1 res) in

  Loops.eq_repeati0 (v table_len - 1)
    (PT.table_select_f (v len) (v table_len) (as_seq h0 table) i) (as_seq h1 res);
  Lib.Loops.for 0ul (table_len -! 1ul) inv
  (fun j ->
    Loops.unfold_repeati (v j + 1)
      (PT.table_select_f (v len) (v table_len) (as_seq h0 table) i) (as_seq h1 res) (v j);
    table_select_consttime_f len table_len table i j res);
  PT.table_select_lemma (v len) (v table_len) (as_seq h0 table) i
