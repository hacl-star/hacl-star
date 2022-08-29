module Hacl.Impl.Exponentiation.Definitions

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module S = Lib.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let inttype_a = t:inttype{t = U32 \/ t = U64}

inline_for_extraction noextract
class to_comm_monoid (a_t:inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) = {
  a_spec: Type0;
  comm_monoid: S.comm_monoid a_spec;
  linv_ctx: x:LSeq.lseq (uint_t a_t SEC) (v ctx_len) -> Type0;
  linv: x:LSeq.lseq (uint_t a_t SEC) (v len) -> Type0;
  refl: x:LSeq.lseq (uint_t a_t SEC) (v len){linv x} -> GTot a_spec;
}


inline_for_extraction noextract
let lone_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (to:to_comm_monoid a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> x:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h x /\ live h ctx /\ disjoint ctx x /\
    to.linv_ctx (as_seq h ctx))
  (ensures  fun h0 _ h1 -> modifies (loc x) h0 h1 /\
    to.linv (as_seq h1 x) /\
    to.refl (as_seq h1 x) == to.comm_monoid.S.one)


inline_for_extraction noextract
let lmul_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (to:to_comm_monoid a_t len ctx_len) =
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
    to.refl (as_seq h1 xy) == to.comm_monoid.S.mul (to.refl (as_seq h0 x)) (to.refl (as_seq h0 y)))


inline_for_extraction noextract
let lsqr_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (to:to_comm_monoid a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> x:lbuffer (uint_t a_t SEC) len
  -> xx:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h x /\ live h xx /\ live h ctx /\
    disjoint x ctx /\ disjoint xx ctx /\ eq_or_disjoint x xx /\
    to.linv (as_seq h x) /\ to.linv_ctx (as_seq h ctx))
  (ensures fun h0 _ h1 -> modifies (loc xx) h0 h1 /\ to.linv (as_seq h1 xx) /\
    to.refl (as_seq h1 xx) == to.comm_monoid.S.mul (refl (as_seq h0 x)) (refl (as_seq h0 x)))


inline_for_extraction noextract
class concrete_ops (a_t:inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) = {
  to: Ghost.erased (to_comm_monoid a_t len ctx_len);
  lone: lone_st a_t len ctx_len to;
  lmul: lmul_st a_t len ctx_len to;
  lsqr: lsqr_st a_t len ctx_len to;
}
