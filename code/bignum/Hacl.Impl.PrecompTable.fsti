module Hacl.Impl.PrecompTable

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module SE = Spec.Exponentiation
module BD = Hacl.Bignum.Definitions

include Hacl.Impl.Exponentiation.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val table_select_consttime:
    #t:BD.limb_t
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
  Math.Lemmas.lemma_mult_le_right (v len) (j + 1) (v table_len);
  let bj = LSeq.sub table (j * v len) (v len) in
  k.to.linv bj /\ k.to.linv a /\
  k.to.refl bj == SE.pow k.to.concr_ops (k.to.refl a) j


// This function computes [a^0 = one; a^1; a^2; ..; a^(table_len - 1)]
inline_for_extraction noextract
val lprecomp_table:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h ctx /\
    disjoint a table /\ disjoint ctx table /\ disjoint a ctx /\
    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx))
  (ensures  fun h0 _ h1 -> modifies (loc table) h0 h1 /\
    (forall (j:nat{j < v table_len}).{:pattern precomp_table_inv len ctx_len k (as_seq h1 a) table_len (as_seq h1 table) j}
      precomp_table_inv len ctx_len k (as_seq h1 a) table_len (as_seq h1 table) j))
