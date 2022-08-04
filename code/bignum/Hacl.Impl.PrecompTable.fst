module Hacl.Impl.PrecompTable

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module BB = Hacl.Bignum.Base
module BD = Hacl.Bignum.Definitions
module PT = Hacl.Spec.PrecompTable
module SE = Spec.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val table_select_consttime_f:
    #t:BD.limb_t
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

// Precomputed table [a^0 = one; a^1; a^2; ..; a^(table_len - 1)]
//----------------------------------------------------------------

inline_for_extraction noextract
val lprecomp_table_mul:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> i:size_t
  -> ti:lbuffer (uint_t a_t SEC) len
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h ti /\ live h ctx /\ live h res /\
    disjoint a ti /\ disjoint a ctx /\ disjoint a res /\
    disjoint ti ctx /\ disjoint ti res /\ disjoint ctx res /\
    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h ti) /\
    k.to.refl (as_seq h ti) == SE.pow k.to.concr_ops (k.to.refl (as_seq h a)) (v i))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) == SE.pow k.to.concr_ops (k.to.refl (as_seq h0 a)) (v i + 1))

let lprecomp_table_mul #a_t len ctx_len k ctx a i ti res =
  let h0 = ST.get () in
  k.lmul ctx a ti res;
  let h1 = ST.get () in
  assert (k.to.refl (as_seq h1 res) == k.to.concr_ops.SE.mul (k.to.refl (as_seq h0 a)) (k.to.refl (as_seq h0 ti)));
  SE.pow_unfold k.to.concr_ops (k.to.refl (as_seq h0 a)) (v i + 1)


#push-options "--z3rlimit 150"
inline_for_extraction noextract
val precomp_table_inv_lemma_j:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> a:LSeq.lseq (uint_t a_t SEC) (v len)
  -> table_len:size_t{v table_len * v len <= max_size_t}
  -> table1:LSeq.lseq (uint_t a_t SEC) (v table_len * v len)
  -> table2:LSeq.lseq (uint_t a_t SEC) (v table_len * v len)
  -> i:nat{i <= v table_len}
  -> j:nat{j < i} -> Lemma
  (requires
    LSeq.sub table1 0 (i * v len) == LSeq.sub table2 0 (i * v len) /\
    precomp_table_inv len ctx_len k a table_len table1 j)
  (ensures
    precomp_table_inv len ctx_len k a table_len table2 j)

let precomp_table_inv_lemma_j #a_t len ctx_len k a table_len table1 table2 i j =
  assert (precomp_table_inv len ctx_len k a table_len table1 j);
  Math.Lemmas.lemma_mult_le_right (v len) (j + 1) (v table_len);
  let bj1 = LSeq.sub table1 (j * v len) (v len) in
  let bj2 = LSeq.sub table2 (j * v len) (v len) in

  let aux (l:nat{l < v len}) : Lemma (LSeq.index bj1 l == LSeq.index bj2 l) =
    Seq.lemma_index_slice table1 (j * v len) (j * v len + v len) l;
    assert (LSeq.index bj1 l == LSeq.index table1 (j * v len + l));
    Seq.lemma_index_slice table2 (j * v len) (j * v len + v len) l;
    assert (LSeq.index bj2 l == LSeq.index table2 (j * v len + l));
    Seq.lemma_index_slice table1 0 (i * v len) (j * v len + l);
    Seq.lemma_index_slice table2 0 (i * v len) (j * v len + l);
    assert (LSeq.index table1 (j * v len + l) == LSeq.index table2 (j * v len + l));
    assert (LSeq.index bj1 l == LSeq.index bj2 l) in

  Classical.forall_intro aux;
  LSeq.eq_intro bj1 bj2;
  assert (precomp_table_inv len ctx_len k a table_len table2 j)
#pop-options


inline_for_extraction noextract
val precomp_table_inv_lemma:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> a:LSeq.lseq (uint_t a_t SEC) (v len)
  -> table_len:size_t{v table_len * v len <= max_size_t}
  -> table1:LSeq.lseq (uint_t a_t SEC) (v table_len * v len)
  -> table2:LSeq.lseq (uint_t a_t SEC) (v table_len * v len)
  -> i:nat{i <= v table_len} -> Lemma
  (requires
    LSeq.sub table1 0 (i * v len) == LSeq.sub table2 0 (i * v len) /\
    (forall (j:nat{j < i}). precomp_table_inv len ctx_len k a table_len table1 j))
  (ensures
    (forall (j:nat{j < i}). precomp_table_inv len ctx_len k a table_len table2 j))

let precomp_table_inv_lemma #a_t len ctx_len k a table_len table1 table2 i =
  let aux (j:nat{j < i}) : Lemma (precomp_table_inv len ctx_len k a table_len table2 j) =
    assert (precomp_table_inv len ctx_len k a table_len table1 j);
    precomp_table_inv_lemma_j #a_t len ctx_len k a table_len table1 table2 i j;
    assert (precomp_table_inv len ctx_len k a table_len table2 j) in

  Classical.forall_intro aux


inline_for_extraction noextract
val lprecomp_table_f:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> i:size_t{v i < v table_len - 1}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h ctx /\
    disjoint a table /\ disjoint ctx table /\ disjoint a ctx /\
    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx) /\
    (forall (j:nat{j <= v i}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc table) h0 h1 /\
    (forall (j:nat{j <= v i + 1}).
      precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) j))

#push-options "--z3rlimit 300"
let lprecomp_table_f #a_t len ctx_len k ctx a table_len i table =
  Math.Lemmas.lemma_mult_le_right (v len) (v i + 1) (v table_len);
  Math.Lemmas.lemma_mult_le_right (v len) (v i + 2) (v table_len);
  assert (v (i *! len) == v i * v len);
  assert (v (i *! len +! len) == v i * v len + v len);

  let h0 = ST.get () in
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h0 table) (v i));
  let t1 = sub table (i *! len) len in
  let t2 = sub table (i *! len +! len) len in
  lprecomp_table_mul len ctx_len k ctx a i t1 t2;
  let h1 = ST.get () in
  B.modifies_buffer_elim (B.gsub #(uint_t a_t SEC) table 0ul (i *! len +! len)) (loc t2) h0 h1;
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) (v i + 1));
  LSeq.eq_intro
    (LSeq.sub (as_seq h0 table) 0 (v i * v len + v len))
    (LSeq.sub (as_seq h1 table) 0 (v i * v len + v len));

  assert (forall (j:nat{j <= v i}).
    precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h0 table) j);
  precomp_table_inv_lemma len ctx_len k (as_seq h0 a) table_len (as_seq h0 table) (as_seq h1 table) (v i + 1);
  assert (forall (j:nat{j <= v i + 1}).
    precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) j)
#pop-options


let lprecomp_table #a_t len ctx_len k ctx a table_len table =
  let t0 = sub table 0ul len in
  let t1 = sub table len len in
  k.lone ctx t0;
  let h0 = ST.get () in
  copy t1 a;
  let h1 = ST.get () in
  //B.modifies_buffer_elim (B.gsub #(uint_t a_t SEC) table 0ul len) (loc t1) h0 h1;
  LSeq.eq_intro (as_seq h0 t0) (as_seq h1 t0);
  assert (k.to.linv (as_seq h1 t0) /\ k.to.linv (as_seq h1 t1));
  SE.pow_eq0 k.to.concr_ops (k.to.refl (as_seq h0 a));
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) 0);

  [@ inline_let]
  let inv h (i:nat{i <= v table_len - 1}) =
    modifies (loc table) h1 h /\
    (forall (j:nat{j < i + 1}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j) in


  Lib.Loops.for 0ul (table_len -! 1ul) inv
  (fun j ->
    lprecomp_table_f #a_t len ctx_len k ctx a table_len j table)
