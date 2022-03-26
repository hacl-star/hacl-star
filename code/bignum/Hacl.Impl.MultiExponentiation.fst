module Hacl.Impl.MultiExponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

module S = Lib.Exponentiation
module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum
module BB = Hacl.Bignum.Base
module SB = Hacl.Spec.Bignum.Base

friend Hacl.Impl.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lexp_double_fw_f_st
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
  -> i:size_t{v i < v bBits / v l}
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
    k.to.linv (as_seq h acc) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a1) table_len (as_seq h table1) j) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a2) table_len (as_seq h table2) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.exp_double_fw_f #k.to.a_spec k.to.comm_monoid
      (k.to.refl (as_seq h0 a1)) (v bBits) (BD.bn_v h0 b1)
      (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l) (v i) (k.to.refl (as_seq h0 acc)))


inline_for_extraction noextract
val lexp_double_fw_f:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_double_fw_f_st a_t len ctx_len k

let lexp_double_fw_f #a_t len ctx_len k lprecomp_get ctx a1 bLen bBits b1 a2 b2 l table_len table1 table2 i acc =
  lexp_fw_f #a_t len ctx_len k lprecomp_get ctx a1 bLen bBits b1 l table_len table1 i acc;
  lmul_acc_pow_a_bits_l len ctx_len k lprecomp_get ctx a2 bLen bBits b2 l table_len table2 i acc


inline_for_extraction noextract
let lexp_double_fw_acc0_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a1:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{0 < v bBits /\ (v bBits - 1) / bits a_t < v bLen}
  -> b1:lbuffer (uint_t a_t SEC) bLen
  -> a2:lbuffer (uint_t a_t SEC) len
  -> b2:lbuffer (uint_t a_t SEC) bLen
  -> l:size_t{0 < v l /\ v l < bits a_t /\ v l < 32}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table1:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> table2:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h -> v bBits % v l <> 0 /\
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
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a1) table_len (as_seq h table1) j) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a2) table_len (as_seq h table2) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.exp_double_fw_acc0 #k.to.a_spec k.to.comm_monoid
      (k.to.refl (as_seq h0 a1)) (v bBits) (BD.bn_v h0 b1)
      (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l))


inline_for_extraction noextract
val lexp_double_fw_acc0:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_double_fw_acc0_st a_t len ctx_len k

let lexp_double_fw_acc0 #a_t len ctx_len k lprecomp_get ctx a1 bLen bBits b1 a2 b2 l table_len table1 table2 acc =
  push_frame ();
  let tmp = create len (uint #a_t #SEC 0) in
  lexp_fw_acc0 #a_t len ctx_len k lprecomp_get ctx a1 bLen bBits b1 l table_len table1 acc;
  lexp_fw_acc0 #a_t len ctx_len k lprecomp_get ctx a2 bLen bBits b2 l table_len table2 tmp;
  k.lmul ctx acc tmp acc;
  pop_frame ()


inline_for_extraction noextract
let lexp_double_fw_loop_st
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
    k.to.linv (as_seq h acc) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a1) table_len (as_seq h table1) j) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a2) table_len (as_seq h table2) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\ k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    Loops.repeati (v bBits / v l) (S.exp_double_fw_f k.to.comm_monoid (k.to.refl (as_seq h0 a1))
      (v bBits) (BD.bn_v h0 b1) (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l)) (k.to.refl (as_seq h0 acc)))


inline_for_extraction noextract
val lexp_double_fw_loop:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_double_fw_loop_st a_t len ctx_len k

let lexp_double_fw_loop #a_t len ctx_len k lprecomp_get ctx a1 bLen bBits b1 a2 b2 l table_len table1 table2 acc =
  let h0 = ST.get () in

  [@ inline_let]
  let refl1 i : GTot k.to.a_spec = k.to.refl (as_seq h0 acc) in
  [@inline_let]
  let spec (h:mem) = S.exp_double_fw_f k.to.comm_monoid (k.to.refl (as_seq h0 a1))
    (v bBits) (BD.bn_v h0 b1) (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l) in

  [@inline_let]
  let inv h (i:nat{i <= v bBits / v l}) =
    modifies (loc acc) h0 h /\
    k.to.linv (as_seq h acc) /\
    k.to.refl (as_seq h acc) == Loops.repeati i (spec h0) (refl1 0) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a1) table_len (as_seq h table1) j) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a2) table_len (as_seq h table2) j) in


  Loops.eq_repeati0 (v bBits / v l) (spec h0) (refl1 0);
  Lib.Loops.for 0ul (bBits /. l) inv
  (fun i ->
    Loops.unfold_repeati (v bBits / v l) (spec h0) (refl1 0) (v i);
    lexp_double_fw_f len ctx_len k lprecomp_get ctx a1 bLen bBits b1 a2 b2 l table_len table1 table2 i acc
  )


inline_for_extraction noextract
let lexp_double_fw_gen_st
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
    k.to.linv (as_seq h acc) /\ k.to.refl (as_seq h acc) == k.to.comm_monoid.S.one /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a1) table_len (as_seq h table1) j) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a2) table_len (as_seq h table2) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.exp_double_fw k.to.comm_monoid
      (k.to.refl (as_seq h0 a1)) (v bBits) (BD.bn_v h0 b1)
      (k.to.refl (as_seq h0 a2)) (BD.bn_v h0 b2) (v l))


inline_for_extraction noextract
val lexp_double_fw_gen_:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_double_fw_gen_st a_t len ctx_len k

let lexp_double_fw_gen_ #a_t len ctx_len k lprecomp_get ctx a1 bLen bBits b1 a2 b2 l table_len table1 table2 acc =
  assert (v (bBits %. l) == v bBits % v l);
  if bBits %. l <> 0ul then
    lexp_double_fw_acc0 len ctx_len k lprecomp_get ctx a1 bLen bBits b1 a2 b2 l table_len table1 table2 acc;

  lexp_double_fw_loop #a_t len ctx_len k lprecomp_get ctx a1 bLen bBits b1 a2 b2 l table_len table1 table2 acc


inline_for_extraction noextract
val lexp_double_fw_gen:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_double_fw_st a_t len ctx_len k

#push-options "--z3rlimit 150"
let lexp_double_fw_gen #a_t len ctx_len k lprecomp_get ctx a1 bLen bBits b1 a2 b2 acc l =
  push_frame ();
  Math.Lemmas.pow2_lt_compat 32 (v l);
  [@inline_let]
  let table_len = 1ul <<. l in
  assert (v table_len == pow2 (v l));
  Math.Lemmas.pow2_le_compat (v l) 1;
  assert (1 < v table_len /\ v table_len * v len <= max_size_t);

  let table1 = create (table_len *! len) (uint #a_t #SEC 0) in
  update_sub table1 0ul len acc;
  lprecomp_table #a_t len ctx_len k ctx a1 table_len table1;
  let h = ST.get () in
  assert (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a1) table_len (as_seq h table1) j);

  let table2 = create (table_len *! len) (uint #a_t #SEC 0) in
  update_sub table2 0ul len acc;
  lprecomp_table #a_t len ctx_len k ctx a2 table_len table2;
  let h = ST.get () in
  assert (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a1) table_len (as_seq h table1) j);
  assert (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a2) table_len (as_seq h table2) j);

  lexp_double_fw_gen_ #a_t len ctx_len k lprecomp_get
    ctx a1 bLen bBits b1 a2 b2 l table_len table1 table2 acc;
  pop_frame ()
#pop-options


let lexp_double_fw_vartime #a_t len ctx_len k ctx a1 bLen bBits b1 a2 b2 acc w =
  lexp_double_fw_gen #a_t len ctx_len k
    (lprecomp_get_vartime #a_t len ctx_len k)
    ctx a1 bLen bBits b1 a2 b2 acc w


let lexp_double_fw_consttime #a_t len ctx_len k ctx a1 bLen bBits b1 a2 b2 acc w =
  lexp_double_fw_gen #a_t len ctx_len k
    (lprecomp_get_consttime #a_t len ctx_len k)
    ctx a1 bLen bBits b1 a2 b2 acc w
