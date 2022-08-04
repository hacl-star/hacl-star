module Hacl.Impl.Exponentiation

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

// This function computes `a^b` using a binary right-to-left method
// It takes variable time to compute the result
inline_for_extraction noextract
val lexp_rl_vartime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h ctx /\
    disjoint a res /\ disjoint b res /\ disjoint a b /\
    disjoint ctx a /\ disjoint ctx res /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a))
  (ensures  fun h0 _ h1 -> modifies (loc a |+| loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) ==
    SE.exp_rl #k.to.t_spec k.to.concr_ops (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b))


// This function computes `a^b` using Montgomery's ladder (a binary method)
// It takes constant time to compute the result
inline_for_extraction noextract
val lexp_mont_ladder_swap_consttime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h ctx /\
    disjoint a res /\ disjoint b res /\ disjoint a b /\
    disjoint ctx a /\ disjoint ctx res /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a))
  (ensures  fun h0 _ h1 -> modifies (loc a |+| loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) ==
    SE.exp_mont_ladder_swap #k.to.t_spec k.to.concr_ops (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b))


// This function computes `a^(2^b)` and writes the result in `res`
inline_for_extraction noextract
val lexp_pow2:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> b:size_t
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h res /\ live h ctx /\ live h a /\
    disjoint res ctx /\ disjoint a ctx /\ disjoint a res /\
    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\ k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) == SE.exp_pow2 k.to.concr_ops (k.to.refl (as_seq h0 a)) (v b))


// This function computes `a^(2^b)` and writes the result in `a`
inline_for_extraction noextract
val lexp_pow2_in_place:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> b:size_t ->
  Stack unit
  (requires fun h ->
    live h a /\ live h ctx /\ disjoint a ctx /\
    k.to.linv (as_seq h a) /\ k.to.linv_ctx (as_seq h ctx))
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\ k.to.linv (as_seq h1 a) /\
    k.to.refl (as_seq h1 a) == SE.exp_pow2 k.to.concr_ops (k.to.refl (as_seq h0 a)) (v b))


// Fixed-window method using a precomputed table
//----------------------------------------------

inline_for_extraction noextract
let size_window_t (a_t:inttype_a) (len:size_t{v len > 0}) =
  l:size_t{0 < v l /\ v l < bits a_t /\ v l < 32 /\ pow2 (v l) * v len <= max_size_t}

inline_for_extraction noextract
let table_len_t (len:size_t{v len > 0}) =
  table_len:size_t{v table_len * v len <= max_size_t}

inline_for_extraction noextract
let table_inv_t (a_t:inttype_a) (len:size_t{v len > 0}) (table_len:table_len_t len) =
  a:LSeq.lseq (uint_t a_t SEC) (v len)
  -> table:LSeq.lseq (uint_t a_t SEC) (v (table_len *! len)) -> GTot Type0


inline_for_extraction noextract
let pow_a_to_small_b_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len)
  (l:size_window_t a_t len)
  (table_len:table_len_t len)
  (table_inv:table_inv_t a_t len table_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> b:uint_t a_t SEC{v b < pow2 (v l)}
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h res /\ live h ctx /\
    disjoint a table /\ disjoint a res /\ disjoint table res /\
    disjoint ctx a /\ disjoint ctx table /\ disjoint ctx res /\
    k.to.linv_ctx (as_seq h ctx) /\ k.to.linv (as_seq h a) /\
    table_inv (as_seq h a) (as_seq h table))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) == SE.pow k.to.concr_ops (k.to.refl (as_seq h0 a)) (v b))


inline_for_extraction noextract
let lexp_fw_table_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len)
  (l:size_window_t a_t len)
  (table_len:table_len_t len)
  (table_inv:table_inv_t a_t len table_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h ctx /\ live h table /\
    disjoint a res /\ disjoint a ctx /\ disjoint a table /\ disjoint b res /\
    disjoint res ctx /\ disjoint res table /\ disjoint ctx table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\ k.to.linv (as_seq h a) /\
    table_inv (as_seq h a) (as_seq h table))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) ==
    SE.exp_fw k.to.concr_ops (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b) (v l))


inline_for_extraction noextract
val mk_lexp_fw_table:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len
  -> table_inv:table_inv_t a_t len table_len
  -> pow_a_to_small_b:pow_a_to_small_b_st a_t len ctx_len k l table_len table_inv ->
  lexp_fw_table_st a_t len ctx_len k l table_len table_inv


// Fixed-window method with a precomputed
// table = [a^0 = one; a^1; a^2; ..; a^(table_len - 1)]
//-----------------------------------------------------

inline_for_extraction noextract
let lexp_fw_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len)
  (l:size_window_t a_t len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h ctx /\
    disjoint a res /\ disjoint a ctx /\
    disjoint b res /\ disjoint res ctx /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) ==
    SE.exp_fw #k.to.t_spec k.to.concr_ops (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b) (v l))


// This function computes `a^b` using a fixed-window method
// It takes variable time to compute the result
inline_for_extraction noextract
val lexp_fw_vartime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len ->
  lexp_fw_st a_t len ctx_len k l


// This function computes `a^b` using a fixed-window method
// It takes constant time to compute the result
inline_for_extraction noextract
val lexp_fw_consttime:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len ->
  lexp_fw_st a_t len ctx_len k l
