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

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let inttype_a = t:inttype{t = U32 \/ t = U64}

inline_for_extraction noextract
class to_concrete_ops (a_t:inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) = {
  t_spec: Type0;
  concr_ops: SE.concrete_ops t_spec;
  linv_ctx: x:LSeq.lseq (uint_t a_t SEC) (v ctx_len) -> Type0;
  linv: x:LSeq.lseq (uint_t a_t SEC) (v len) -> Type0;
  refl: x:LSeq.lseq (uint_t a_t SEC) (v len){linv x} -> GTot t_spec;
}


inline_for_extraction noextract
let lone_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (to:to_concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> x:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h x /\ live h ctx /\ disjoint ctx x /\
    to.linv_ctx (as_seq h ctx))
  (ensures  fun h0 _ h1 -> modifies (loc x) h0 h1 /\
    to.linv (as_seq h1 x) /\
    to.refl (as_seq h1 x) == to.concr_ops.SE.one ())


inline_for_extraction noextract
let lmul_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (to:to_concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> x:lbuffer (uint_t a_t SEC) len
  -> y:lbuffer (uint_t a_t SEC) len
  -> xy:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h xy /\ live h ctx /\
    eq_or_disjoint x xy /\ eq_or_disjoint y xy /\ eq_or_disjoint x y /\
    disjoint ctx x /\ disjoint ctx y /\ disjoint ctx xy /\
    to.linv (as_seq h x) /\ to.linv (as_seq h y) /\ to.linv_ctx (as_seq h ctx))
  (ensures fun h0 _ h1 -> modifies (loc xy) h0 h1 /\ to.linv (as_seq h1 xy) /\
    to.refl (as_seq h1 xy) == to.concr_ops.SE.mul (to.refl (as_seq h0 x)) (to.refl (as_seq h0 y)))


inline_for_extraction noextract
let lsqr_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (to:to_concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> x:lbuffer (uint_t a_t SEC) len
  -> xx:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h x /\ live h xx /\ live h ctx /\
    disjoint x ctx /\ disjoint xx ctx /\ eq_or_disjoint x xx /\
    to.linv (as_seq h x) /\ to.linv_ctx (as_seq h ctx))
  (ensures fun h0 _ h1 -> modifies (loc xx) h0 h1 /\ to.linv (as_seq h1 xx) /\
    to.refl (as_seq h1 xx) == to.concr_ops.SE.sqr (refl (as_seq h0 x)))


inline_for_extraction noextract
class concrete_ops (a_t:inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) = {
  to: Ghost.erased (to_concrete_ops a_t len ctx_len);
  lone: lone_st a_t len ctx_len to;
  lmul: lmul_st a_t len ctx_len to;
  lsqr: lsqr_st a_t len ctx_len to;
}


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

//-----------------------------------------

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
let table_inv_precomp
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len)
  (l:size_window_t a_t len)
  (table_len:table_len_t len) : table_inv_t a_t len table_len =
  fun a table ->
    1 < v table_len /\ v table_len = pow2 (v l) /\
      (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k a table_len table j)


// This function returns table.[bits_l] = a^bits_l
// It takes variable time to access bits_l-th element of a table
inline_for_extraction noextract
val lprecomp_get_vartime:
     #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len ->
  pow_a_to_small_b_st a_t len ctx_len k l table_len
    (table_inv_precomp a_t len ctx_len k l table_len)


// This function returns table.[bits_l] = a^bits_l
// It takes constant time to access bits_l-th element of a table
inline_for_extraction noextract
val lprecomp_get_consttime:
     #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len ->
  pow_a_to_small_b_st a_t len ctx_len k l table_len
    (table_inv_precomp a_t len ctx_len k l table_len)

//-----------------------------

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
