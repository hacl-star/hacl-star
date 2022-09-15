module Hacl.Impl.MultiExponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module S = Lib.Exponentiation
module BD = Hacl.Bignum.Definitions

open Hacl.Impl.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// Double Fixed-window method using two precomputed tables
//---------------------------------------------------------

inline_for_extraction noextract
let lexp_double_fw_tables_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len)
  (l:size_window_t a_t len)
  (table_len:table_len_t len)
  (table_inv1:table_inv_t a_t len table_len)
  (table_inv2:table_inv_t a_t len table_len)
  =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a1:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b1:lbuffer (uint_t a_t SEC) bLen
  -> a2:lbuffer (uint_t a_t SEC) len
  -> b2:lbuffer (uint_t a_t SEC) bLen
  -> table1:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> table2:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a1 /\ live h b1 /\ live h a2 /\ live h b2 /\
    live h res /\ live h ctx /\ live h table1 /\ live h table2 /\

    eq_or_disjoint a1 a2 /\ disjoint a1 res /\ disjoint a1 ctx /\
    disjoint b1 res /\ disjoint a2 res /\ disjoint a2 ctx /\
    disjoint b2 res /\ disjoint res ctx /\ disjoint res table1 /\ disjoint res table2 /\

    BD.bn_v h b1 < pow2 (v bBits) /\
    BD.bn_v h b2 < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a1) /\ k.to.linv (as_seq h a2) /\
    table_inv1 (as_seq h a1) (as_seq h table1) /\
    table_inv2 (as_seq h a2) (as_seq h table2))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) ==
    S.exp_double_fw k.to.comm_monoid
      (k.to.refl (as_seq h0 a1)) (v bBits) (BD.bn_v h0 b1)
      (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l))


inline_for_extraction noextract
val mk_lexp_double_fw_tables:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len
  -> table_inv1:table_inv_t a_t len table_len
  -> table_inv2:table_inv_t a_t len table_len
  -> pow_a_to_small_b1:pow_a_to_small_b_st a_t len ctx_len k l table_len table_inv1
  -> pow_a_to_small_b2:pow_a_to_small_b_st a_t len ctx_len k l table_len table_inv2 ->
  lexp_double_fw_tables_st a_t len ctx_len k l table_len table_inv1 table_inv2


// Double Fixed-window method with two precomputed tables
// table1 = [a1^0 = one; a1^1; a1^2; ..; a1^(table_len - 1)]
// table2 = [a2^0 = one; a2^1; a2^2; ..; a2^(table_len - 1)]
//-----------------------------------------------------------

inline_for_extraction noextract
let lexp_double_fw_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len)
  (l:size_window_t a_t len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a1:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b1:lbuffer (uint_t a_t SEC) bLen
  -> a2:lbuffer (uint_t a_t SEC) len
  -> b2:lbuffer (uint_t a_t SEC) bLen
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a1 /\ live h b1 /\ live h a2 /\ live h b2 /\ live h res /\ live h ctx /\
    eq_or_disjoint a1 a2 /\ disjoint a1 res /\ disjoint a1 ctx /\
    disjoint a2 res /\ disjoint a2 ctx /\
    disjoint res b1 /\ disjoint res b2 /\ disjoint res ctx /\
    BD.bn_v h b1 < pow2 (v bBits) /\
    BD.bn_v h b2 < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a1) /\ k.to.linv (as_seq h a2))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) ==
    S.exp_double_fw #k.to.a_spec k.to.comm_monoid
      (k.to.refl (as_seq h0 a1)) (v bBits) (BD.bn_v h0 b1)
      (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l))


// This function computes `a1^b1 `mul` a2^b2` using a fixed-window method
// It takes variable time to compute the result
inline_for_extraction noextract
val lexp_double_fw_vartime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len ->
  lexp_double_fw_st a_t len ctx_len k l


// This function computes `a1^b1 `mul` a2^b2` using a fixed-window method
// It takes constant time to compute the result
inline_for_extraction noextract
val lexp_double_fw_consttime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len ->
  lexp_double_fw_st a_t len ctx_len k l
