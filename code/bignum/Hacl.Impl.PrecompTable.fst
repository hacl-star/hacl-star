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
module S = Lib.Exponentiation.Definition

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// val lemma_table_sub_len: len:nat -> table_len:nat -> i:nat{i < table_len} ->
//   Lemma (i * len + len <= table_len * len)
let lemma_table_sub_len len table_len i =
  Math.Lemmas.distributivity_add_left i 1 len;
  Math.Lemmas.lemma_mult_le_right len (i + 1) table_len

inline_for_extraction noextract
let table_gsub_len
  (#bt:buftype)
  (#t:BD.limb_t)
  (len:size_t{v len > 0})
  (table_len:size_t{v table_len * v len <= max_size_t})
  (table:lbuffer_t bt (uint_t t SEC) (table_len *! len))
  (i:size_t{v i < v table_len}) : GTot (lbuffer_t bt (uint_t t SEC) len) =

  lemma_table_sub_len (v len) (v table_len) (v i);
  gsub table (i *! len) len


inline_for_extraction noextract
val table_sub_len:
    #bt:buftype
  -> #t:BD.limb_t
  -> len:size_t{v len > 0}
  -> table_len:size_t{v table_len * v len <= max_size_t}
  -> table:lbuffer_t bt (uint_t t SEC) (table_len *! len)
  -> i:size_t{v i < v table_len} ->
  Stack (lbuffer_t bt (uint_t t SEC) len)
  (requires fun h -> live h table)
  (ensures  fun h0 r h1 -> h0 == h1 /\ live h1 r /\
    r == table_gsub_len len table_len table i /\
    as_seq h1 r == spec_table_sub_len (v len) (v table_len) (as_seq h0 table) (v i) /\
    B.loc_includes (loc table) (loc r))

let table_sub_len #t len table_len table i =
  lemma_table_sub_len (v len) (v table_len) (v i);
  sub table (i *! len) len

//------------------------------

inline_for_extraction noextract
let spec_table_update_sub_len
  (#t:BD.limb_t)
  (len:pos)
  (table_len:size_nat{table_len * len <= max_size_t})
  (table:LSeq.lseq (uint_t t SEC) (table_len * len))
  (i:nat{i < table_len})
  (b:LSeq.lseq (uint_t t SEC) len) : LSeq.lseq (uint_t t SEC) (table_len * len) =

  lemma_table_sub_len len table_len i;
  LSeq.update_sub table (i * len) len b


inline_for_extraction noextract
val table_update_sub_len:
    #t:BD.limb_t
  -> len:size_t{v len > 0}
  -> table_len:size_t{v table_len * v len <= max_size_t}
  -> table:lbuffer (uint_t t SEC) (table_len *! len)
  -> i:size_t{v i < v table_len}
  -> b:lbuffer (uint_t t SEC) len ->
  Stack unit
  (requires fun h ->
    live h table /\ live h b /\ disjoint table b)
  (ensures  fun h0 r h1 -> modifies (loc table) h0 h1 /\
    as_seq h1 table ==
    spec_table_update_sub_len (v len) (v table_len) (as_seq h0 table) (v i) (as_seq h0 b))

let table_update_sub_len #t len table_len table i b =
  lemma_table_sub_len (v len) (v table_len) (v i);
  update_sub table (i *! len) len b

//-------------------------------------

inline_for_extraction noextract
val table_select_consttime_f:
    #t:BD.limb_t
  -> len:size_t{v len > 0}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:clbuffer (uint_t t SEC) (table_len *! len)
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
  let res_j = table_sub_len len table_len table (j +! 1ul) in
  map2T len acc (BB.mask_select c) res_j acc


let table_select_consttime #t len table_len table i res =
  let h0 = ST.get () in
  copy res (table_sub_len len table_len table 0ul);

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
    k.to.refl (as_seq h ti) == S.pow k.to.comm_monoid (k.to.refl (as_seq h a)) (2 * v i + 2))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) == S.pow k.to.comm_monoid (k.to.refl (as_seq h0 a)) (2 * v i + 3))

let lprecomp_table_mul #a_t len ctx_len k ctx a i ti res =
  let h0 = ST.get () in
  k.lmul ctx a ti res;
  let h1 = ST.get () in
  assert (k.to.refl (as_seq h1 res) ==
    k.to.comm_monoid.S.mul (k.to.refl (as_seq h0 a)) (k.to.refl (as_seq h0 ti)));
  k.to.comm_monoid.lemma_mul_comm (k.to.refl (as_seq h0 a)) (k.to.refl (as_seq h0 ti));
  S.lemma_pow_add k.to.comm_monoid (k.to.refl (as_seq h0 a)) (2 * v i + 2) 1;
  S.lemma_pow1 k.to.comm_monoid (k.to.refl (as_seq h0 a))


inline_for_extraction noextract
val lprecomp_table_sqr:
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
    k.to.refl (as_seq h ti) == S.pow k.to.comm_monoid (k.to.refl (as_seq h a)) (v i + 1))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) == S.pow k.to.comm_monoid (k.to.refl (as_seq h0 a)) (2 * v i + 2))

let lprecomp_table_sqr #a_t len ctx_len k ctx a i ti res =
  let h0 = ST.get () in
  k.lsqr ctx ti res;
  let h1 = ST.get () in
  assert (k.to.refl (as_seq h1 res) ==
    k.to.comm_monoid.S.mul (k.to.refl (as_seq h0 ti)) (k.to.refl (as_seq h0 ti)));
  S.lemma_pow_add k.to.comm_monoid (k.to.refl (as_seq h0 a)) (v i + 1) (v i + 1)


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
  let bj1 = spec_table_sub_len (v len) (v table_len) table1 j in
  let bj2 = spec_table_sub_len (v len) (v table_len) table2 j in

  let aux (l:nat{l < v len}) : Lemma (LSeq.index bj1 l == LSeq.index bj2 l) =
    lemma_table_sub_len (v len) (v table_len) j;
    assert (j * v len + v len <= v table_len * v len);
    Seq.lemma_index_slice table1 (j * v len) (j * v len + v len) l;
    assert (LSeq.index bj1 l == LSeq.index table1 (j * v len + l));
    Seq.lemma_index_slice table2 (j * v len) (j * v len + v len) l;
    assert (LSeq.index bj2 l == LSeq.index table2 (j * v len + l));

    Math.Lemmas.lemma_mult_le_right (v len) i (v table_len);
    assert (i * v len <= v table_len * v len);

    Math.Lemmas.distributivity_add_left j 1 (v len);
    Math.Lemmas.lemma_mult_lt_right (v len) j i;
    assert (j * v len + l < i * v len);
    Seq.lemma_index_slice table1 0 (i * v len) (j * v len + l);
    Seq.lemma_index_slice table2 0 (i * v len) (j * v len + l);
    assert (LSeq.index table1 (j * v len + l) == LSeq.index table2 (j * v len + l));
    assert (LSeq.index bj1 l == LSeq.index bj2 l) in

  Classical.forall_intro aux;
  LSeq.eq_intro bj1 bj2;
  assert (precomp_table_inv len ctx_len k a table_len table2 j)


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
val table_update_sub_len_inv:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len % 2 = 0}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> i:size_t{v i < v table_len}
  -> b:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h ctx /\ live h b /\
    disjoint a table /\ disjoint ctx table /\ disjoint a ctx /\ disjoint b table /\
    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx) /\ k.to.linv (as_seq h b) /\
    k.to.refl (as_seq h b) == S.pow k.to.comm_monoid (k.to.refl (as_seq h a)) (v i) /\
    (forall (j:nat{j < v i}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 r h1 -> modifies (loc table) h0 h1 /\
    as_seq h1 table ==
    spec_table_update_sub_len (v len) (v table_len) (as_seq h0 table) (v i) (as_seq h0 b) /\
    (forall (j:nat{j < v i + 1}).
      precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) j))

let table_update_sub_len_inv #a_t len ctx_len k ctx a table_len table i b =
  let h0 = ST.get () in
  table_update_sub_len len table_len table i b;
  let h1 = ST.get () in
  lemma_table_sub_len (v len) (v table_len) (v i);
  assert (as_seq h1 table ==
    LSeq.update_sub (as_seq h0 table) (v i * v len) (v len) (as_seq h0 b));
  LSeq.eq_intro
    (LSeq.sub (as_seq h0 table) 0 (v i * v len))
    (LSeq.sub (as_seq h1 table) 0 (v i * v len));
  assert (forall (j:nat{j < v i}).
    precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h0 table) j);
  precomp_table_inv_lemma len ctx_len k (as_seq h0 a)
    table_len (as_seq h0 table) (as_seq h1 table) (v i);
  assert (forall (j:nat{j < v i}).
    precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) j);
  assert (forall (j:nat{j < v i + 1}).
    precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) j)


inline_for_extraction noextract
val lprecomp_table_f_sqr:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len % 2 = 0}
  -> i:size_t{v i < (v table_len - 2) / 2}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> tmp:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h ctx /\ live h tmp /\
    disjoint a table /\ disjoint ctx table /\ disjoint a ctx /\
    disjoint tmp table /\ disjoint tmp ctx /\ disjoint tmp a /\

    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx) /\
    (forall (j:nat{j <= 2 * v i + 1}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc table |+| loc tmp) h0 h1 /\
    (forall (j:nat{j <= 2 * v i + 2}).
      precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) j))

let lprecomp_table_f_sqr #a_t len ctx_len k ctx a table_len i table tmp =
  assert (v i + 1 < v table_len);
  let t1 = table_sub_len len table_len table (i +! 1ul) in
  let h0 = ST.get () in
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h0 table) (v i + 1));
  lprecomp_table_sqr len ctx_len k ctx a i t1 tmp;
  assert (2 * v i + 2 < v table_len);
  table_update_sub_len_inv len ctx_len k ctx a table_len table (2ul *! i +! 2ul) tmp


inline_for_extraction noextract
val lprecomp_table_f_mul:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len % 2 = 0}
  -> i:size_t{v i < (v table_len - 2) / 2}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> tmp:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h ctx /\ live h tmp /\
    disjoint a table /\ disjoint ctx table /\ disjoint a ctx /\
    disjoint tmp table /\ disjoint tmp ctx /\ disjoint tmp a /\

    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx) /\
    (forall (j:nat{j <= 2 * v i + 2}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc table |+| loc tmp) h0 h1 /\
    (forall (j:nat{j <= 2 * v i + 3}).
      precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) j))

let lprecomp_table_f_mul #a_t len ctx_len k ctx a table_len i table tmp =
  assert (2 * v i + 2 < v table_len);
  let t2 = table_sub_len len table_len table (2ul *! i +! 2ul) in
  let h0 = ST.get () in
  assert (precomp_table_inv len ctx_len k (as_seq h0 a)
    table_len (as_seq h0 table) (2 * v i + 2));
  lprecomp_table_mul len ctx_len k ctx a i t2 tmp;
  assert (2 * v i + 3 < v table_len);
  table_update_sub_len_inv len ctx_len k ctx a table_len table (2ul *! i +! 3ul) tmp


inline_for_extraction noextract
val lprecomp_table_f:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len % 2 = 0}
  -> i:size_t{v i < (v table_len - 2) / 2}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> tmp:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h ctx /\ live h tmp /\
    disjoint a table /\ disjoint ctx table /\ disjoint a ctx /\
    disjoint tmp table /\ disjoint tmp ctx /\ disjoint tmp a /\

    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx) /\
    (forall (j:nat{j <= 2 * v i + 1}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc table |+| loc tmp) h0 h1 /\
    (forall (j:nat{j <= 2 * v i + 3}).
      precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) j))

let lprecomp_table_f #a_t len ctx_len k ctx a table_len i table tmp =
  lprecomp_table_f_sqr #a_t len ctx_len k ctx a table_len i table tmp;
  lprecomp_table_f_mul #a_t len ctx_len k ctx a table_len i table tmp


inline_for_extraction noextract
val lprecomp_table_noalloc:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len % 2 = 0}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> tmp:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h ctx /\ live h tmp /\
    disjoint a table /\ disjoint ctx table /\ disjoint a ctx /\
    disjoint tmp table /\ disjoint tmp ctx /\ disjoint tmp a /\
    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx))
  (ensures  fun h0 _ h1 -> modifies (loc table |+| loc tmp) h0 h1 /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h1 a) table_len (as_seq h1 table) j))

let lprecomp_table_noalloc #a_t len ctx_len k ctx a table_len table tmp =
  let t0 = sub table 0ul len in
  let t1 = sub table len len in
  k.lone ctx t0;
  let h0 = ST.get () in
  copy t1 a;
  let h1 = ST.get () in
  //B.modifies_buffer_elim (B.gsub #(uint_t a_t SEC) table 0ul len) (loc t1) h0 h1;
  LSeq.eq_intro (as_seq h0 t0) (as_seq h1 t0);
  assert (k.to.linv (as_seq h1 t0) /\ k.to.linv (as_seq h1 t1));
  S.lemma_pow0 k.to.comm_monoid (k.to.refl (as_seq h0 a));
  S.lemma_pow1 k.to.comm_monoid (k.to.refl (as_seq h0 a));
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) 0);
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h1 table) 1);

  [@ inline_let]
  let inv h (i:nat{i <= (v table_len - 2) / 2}) =
    modifies (loc table |+| loc tmp) h1 h /\
    (forall (j:nat{j < 2 * i + 2}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j) in

  [@inline_let]
  let nb = (table_len -! 2ul) /. 2ul in

  Lib.Loops.for 0ul nb inv
  (fun j ->
    lprecomp_table_f len ctx_len k ctx a table_len j table tmp)


let lprecomp_table #a_t len ctx_len k ctx a table_len table =
  push_frame ();
  let tmp = create len (uint #a_t #SEC 0) in
  lprecomp_table_noalloc len ctx_len k ctx a table_len table tmp;
  pop_frame ()

//----------------

let lprecomp_get_vartime #a_t len ctx_len k a table_len table bits_l tmp =
  let bits_l32 = Lib.RawIntTypes.(size_from_UInt32 (u32_to_UInt32 (to_u32 bits_l))) in
  assert (v bits_l32 == v bits_l /\ v bits_l < v table_len);

  let h0 = ST.get () in
  let a_bits_l = table_sub_len len table_len table bits_l32 in
  let h1 = ST.get () in
  assert (precomp_table_inv len ctx_len k a table_len (as_seq h0 table) (v bits_l));
  assert (k.to.refl (as_seq h1 a_bits_l) == S.pow k.to.comm_monoid (k.to.refl a) (v bits_l));
  copy tmp a_bits_l


let lprecomp_get_consttime #a_t len ctx_len k a table_len table bits_l tmp =
  let h0 = ST.get () in
  table_select_consttime len table_len table bits_l tmp;
  let h1 = ST.get () in
  assert (precomp_table_inv len ctx_len k a table_len (as_seq h0 table) (v bits_l));
  assert (k.to.refl (as_seq h1 tmp) == S.pow k.to.comm_monoid (k.to.refl a) (v bits_l))
