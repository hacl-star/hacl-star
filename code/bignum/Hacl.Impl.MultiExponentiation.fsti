module Hacl.Impl.MultiExponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module SE = Spec.Exponentiation
module BD = Hacl.Bignum.Definitions

open Hacl.Impl.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lexp_double_fw_tables_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a1:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b1:lbuffer (uint_t a_t SEC) bLen
  -> a2:lbuffer (uint_t a_t SEC) len
  -> b2:lbuffer (uint_t a_t SEC) bLen
  -> l:size_t{0 < v l /\ v l < bits a_t /\ v l < 32}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table1:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> table2:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a1 /\ live h b1 /\ live h a2 /\ live h b2 /\
    live h acc /\ live h ctx /\ live h table1 /\ live h table2 /\

    eq_or_disjoint a1 a2 /\ disjoint a1 acc /\ disjoint a1 ctx /\
    disjoint a1 table1 /\ disjoint a1 table2 /\ disjoint b1 acc /\
    disjoint a2 acc /\ disjoint a2 ctx /\ disjoint a2 table1 /\ disjoint a2 table2 /\
    disjoint b2 acc /\ disjoint acc ctx /\ disjoint acc table1 /\ disjoint acc table2 /\
    disjoint ctx table1 /\ disjoint ctx table2 /\ eq_or_disjoint table1 table2 /\

    BD.bn_v h b1 < pow2 (v bBits) /\
    BD.bn_v h b2 < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a1) /\ k.to.linv (as_seq h a2) /\
    k.to.linv (as_seq h acc) /\ k.to.refl (as_seq h acc) == k.to.concr_ops.SE.one () /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a1) table_len (as_seq h table1) j) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a2) table_len (as_seq h table2) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    SE.exp_double_fw k.to.concr_ops
      (k.to.refl (as_seq h0 a1)) (v bBits) (BD.bn_v h0 b1)
      (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l))


// This function computes `a1^b1 `mul` a2^b2` using a fixed-window method
// It takes variable time to compute the result
// The function also expects precomputed tables for `a1` and `a2`, i.e.,
// table1 = [a1^0 = one; a1^1; a1^2; ..; a1^(table_len - 1)]
// table2 = [a2^0 = one; a2^1; a2^2; ..; a2^(table_len - 1)]
inline_for_extraction noextract
val lexp_double_fw_tables_vartime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len ->
  lexp_double_fw_tables_st a_t len ctx_len k


// This function computes `a1^b1 `mul` a2^b2` using a fixed-window method
// It takes constant time to compute the result
// The function also expects precomputed tables for `a1` and `a2`, i.e.,
// table1 = [a1^0 = one; a1^1; a1^2; ..; a1^(table_len - 1)]
// table2 = [a2^0 = one; a2^1; a2^2; ..; a2^(table_len - 1)]
inline_for_extraction noextract
val lexp_double_fw_tables_consttime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len ->
  lexp_double_fw_tables_st a_t len ctx_len k


inline_for_extraction noextract
let lexp_double_fw_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a1:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b1:lbuffer (uint_t a_t SEC) bLen
  -> a2:lbuffer (uint_t a_t SEC) len
  -> b2:lbuffer (uint_t a_t SEC) bLen
  -> acc:lbuffer (uint_t a_t SEC) len
  -> l:size_t{0 < v l /\ v l < bits a_t /\ pow2 (v l) * v len <= max_size_t /\ v l < 32} ->
  Stack unit
  (requires fun h ->
    live h a1 /\ live h b1 /\ live h a2 /\ live h b2 /\ live h acc /\ live h ctx /\
    eq_or_disjoint a1 a2 /\ disjoint a1 acc /\ disjoint a1 ctx /\
    disjoint a2 acc /\ disjoint a2 ctx /\
    disjoint acc b1 /\ disjoint acc b2 /\ disjoint acc ctx /\
    BD.bn_v h b1 < pow2 (v bBits) /\
    BD.bn_v h b2 < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a1) /\ k.to.linv (as_seq h a2) /\
    k.to.linv (as_seq h acc) /\ k.to.refl (as_seq h acc) == k.to.concr_ops.SE.one ())
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    SE.exp_double_fw #k.to.t_spec k.to.concr_ops
      (k.to.refl (as_seq h0 a1)) (v bBits) (BD.bn_v h0 b1)
      (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l))


// This function computes `a1^b1 `mul` a2^b2` using a fixed-window method
// It takes variable time to compute the result
inline_for_extraction noextract
val lexp_double_fw_vartime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len ->
  lexp_double_fw_st a_t len ctx_len k


// This function computes `a1^b1 `mul` a2^b2` using a fixed-window method
// It takes constant time to compute the result
inline_for_extraction noextract
val lexp_double_fw_consttime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len ->
  lexp_double_fw_st a_t len ctx_len k
