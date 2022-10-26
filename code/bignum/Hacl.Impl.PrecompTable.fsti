module Hacl.Impl.PrecompTable

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module S = Lib.Exponentiation
module BD = Hacl.Bignum.Definitions

include Hacl.Impl.Exponentiation.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_table_sub_len: len:nat -> table_len:nat -> i:nat{i < table_len} ->
  Lemma (i * len + len <= table_len * len)

inline_for_extraction noextract
let spec_table_sub_len
  (#t:BD.limb_t)
  (len:pos)
  (table_len:size_nat{table_len * len <= max_size_t})
  (table:LSeq.lseq (uint_t t SEC) (table_len * len))
  (i:nat{i < table_len}) : LSeq.lseq (uint_t t SEC) len =

  lemma_table_sub_len len table_len i;
  LSeq.sub table (i * len) len


inline_for_extraction noextract
val table_select_consttime:
    #t:BD.limb_t
  -> len:size_t{v len > 0}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:clbuffer (uint_t t SEC) (table_len *! len)
  -> i:uint_t t SEC{v i < v table_len}
  -> res:lbuffer (uint_t t SEC) len ->
  Stack unit
  (requires fun h ->
    live h table /\ live h res /\ disjoint table res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == spec_table_sub_len (v len) (v table_len) (as_seq h0 table) (v i))


// Precomputed table [a^0 = one; a^1; a^2; ..; a^(table_len - 1)]
//----------------------------------------------------------------

inline_for_extraction noextract
let precomp_table_inv
  (#a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len)
  (a:LSeq.lseq (uint_t a_t SEC) (v len))
  (table_len:size_t{v table_len * v len <= max_size_t})
  (table:LSeq.lseq (uint_t a_t SEC) (v table_len * v len))
  (j:nat{j < v table_len}) : Type0
 =
  let bj = spec_table_sub_len (v len) (v table_len) table j in
  k.to.linv bj /\ k.to.linv a /\
  k.to.refl bj == S.pow k.to.comm_monoid (k.to.refl a) j


// This function computes [a^0 = one; a^1; a^2; ..; a^(table_len - 1)]
inline_for_extraction noextract
val lprecomp_table:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len % 2 = 0}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h ctx /\
    disjoint a table /\ disjoint ctx table /\ disjoint a ctx /\
    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx))
  (ensures  fun h0 _ h1 -> modifies (loc table) h0 h1 /\
    (forall (j:nat{j < v table_len}).{:pattern precomp_table_inv len ctx_len k (as_seq h1 a) table_len (as_seq h1 table) j}
      precomp_table_inv len ctx_len k (as_seq h1 a) table_len (as_seq h1 table) j))


inline_for_extraction noextract
let lprecomp_get_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    a:Ghost.erased (LSeq.lseq (uint_t a_t SEC) (v len))
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:clbuffer (uint_t a_t SEC) (table_len *! len)
  -> bits_l:uint_t a_t SEC{v bits_l < v table_len}
  -> tmp:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h table /\ live h tmp /\ disjoint table tmp /\
    k.to.linv a /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k a table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    k.to.linv (as_seq h1 tmp) /\
    k.to.refl (as_seq h1 tmp) == S.pow k.to.comm_monoid (k.to.refl a) (v bits_l))


// This function returns table.[bits_l] = a^bits_l
// It takes variable time to access bits_l-th element of a table
inline_for_extraction noextract
val lprecomp_get_vartime:
     #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len ->
  lprecomp_get_st a_t len ctx_len k


// This function returns table.[bits_l] = a^bits_l
// It takes variable time to access bits_l-th element of a table
inline_for_extraction noextract
val lprecomp_get_consttime:
     #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len ->
  lprecomp_get_st a_t len ctx_len k
