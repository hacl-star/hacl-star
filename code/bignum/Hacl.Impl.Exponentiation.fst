module Hacl.Impl.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum
module BB = Hacl.Bignum.Base
module PT = Hacl.Impl.PrecompTable


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let lexp_rl_vartime #a_t len ctx_len k ctx a bLen bBits b acc =
  k.lone ctx acc;
  let h0 = ST.get () in

  [@inline_let]
  let refl1 i : GTot (k.to.t_spec & k.to.t_spec) =
    (refl (as_seq h0 acc), refl (as_seq h0 a)) in

  [@inline_let]
  let spec (h:mem) = SE.exp_rl_f k.to.concr_ops (v bBits) (BD.bn_v h0 b) in

  [@inline_let]
  let inv h (i:nat{i <= v bBits}) =
    modifies (loc a |+| loc acc) h0 h /\
    k.to.linv (as_seq h a) /\
    k.to.linv (as_seq h acc) /\
   (let res = Loops.repeati i (spec h0) (refl1 0) in
    fst res == k.to.refl (as_seq h acc) /\
    snd res == k.to.refl (as_seq h a)) in

  Loops.eq_repeati0 (v bBits) (spec h0) (refl1 0);
  Lib.Loops.for 0ul bBits inv
  (fun i ->
    Loops.unfold_repeati (v bBits) (spec h0) (refl1 0) (v i);
    let bit = BN.bn_get_ith_bit bLen b i in
    SN.bn_get_ith_bit_lemma (as_seq h0 b) (v i);

    if not (BB.unsafe_bool_of_limb0 bit) then
      k.lmul ctx acc a acc; // acc = (acc * a) % n
    k.lsqr ctx a a // a = (a * a) % n
  )


inline_for_extraction noextract
val cswap2:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> bit:uint_t a_t SEC{v bit <= 1}
  -> p1:lbuffer (uint_t a_t SEC) len
  -> p2:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h p1 /\ live h p2 /\ disjoint p1 p2 /\
    k.to.linv (as_seq h p1) /\ k.to.linv (as_seq h p2))
  (ensures  fun h0 _ h1 -> modifies (loc p1 |+| loc p2) h0 h1 /\
    k.to.linv (as_seq h1 p1) /\ k.to.linv (as_seq h1 p2) /\
    (k.to.refl (as_seq h1 p1), k.to.refl (as_seq h1 p2)) ==
    LE.cswap (v bit) (k.to.refl (as_seq h0 p1)) (k.to.refl (as_seq h0 p2)))

let cswap2 #a_t len ctx_len k bit p1 p2 =
  let h0 = ST.get () in
  BN.cswap2 len bit p1 p2;
  SN.cswap2_lemma bit (as_seq h0 p1) (as_seq h0 p2)


val lemma_bit_xor_is_sum_mod2: #a_t:inttype_a -> a:uint_t a_t SEC -> b:uint_t a_t SEC -> Lemma
  (requires v a <= 1 /\ v b <= 1)
  (ensures  v (a ^. b) == (v a + v b) % 2)

let lemma_bit_xor_is_sum_mod2 #a_t a b =
  match a_t with
  | U32 ->
    logxor_spec a b;
    assert_norm (UInt32.logxor 0ul 0ul == 0ul);
    assert_norm (UInt32.logxor 0ul 1ul == 1ul);
    assert_norm (UInt32.logxor 1ul 0ul == 1ul);
    assert_norm (UInt32.logxor 1ul 1ul == 0ul)
  | U64 ->
    logxor_spec a b;
    assert_norm (UInt64.logxor 0uL 0uL == 0uL);
    assert_norm (UInt64.logxor 0uL 1uL == 1uL);
    assert_norm (UInt64.logxor 1uL 0uL == 1uL);
    assert_norm (UInt64.logxor 1uL 1uL == 0uL)


//r0 = acc; r1 = a
let lexp_mont_ladder_swap_consttime #a_t len ctx_len k ctx a bLen bBits b acc =
  push_frame ();
  let sw = create 1ul (uint #a_t #SEC 0) in

  k.lone ctx acc;
  let h0 = ST.get () in

  [@inline_let]
  let refl1 i : GTot (k.to.t_spec & k.to.t_spec & nat) =
    (k.to.refl (as_seq h0 acc), k.to.refl (as_seq h0 a), v (LSeq.index (as_seq h0 sw) 0)) in

  [@inline_let]
  let spec (h:mem) = SE.exp_mont_ladder_swap_f k.to.concr_ops (v bBits) (BD.bn_v h0 b) in

  [@inline_let]
  let inv h (i:nat{i <= v bBits}) =
    modifies (loc a |+| loc acc |+| loc sw) h0 h /\
    k.to.linv (as_seq h a) /\
    k.to.linv (as_seq h acc) /\
    v (LSeq.index (as_seq h sw) 0) <= 1 /\
   (let (acc1, a1, sw1) = Loops.repeati i (spec h0) (refl1 0) in
    a1 == k.to.refl (as_seq h a) /\
    acc1 == k.to.refl (as_seq h acc) /\
    sw1 == v (LSeq.index (as_seq h sw) 0)) in

  Loops.eq_repeati0 (v bBits) (spec h0) (refl1 0);
  Lib.Loops.for 0ul bBits inv
  (fun i ->
    let h2 = ST.get () in
    Loops.unfold_repeati (v bBits) (spec h0) (refl1 0) (v i);
    let bit = BN.bn_get_ith_bit bLen b (bBits -! i -! 1ul) in
    SN.bn_get_ith_bit_lemma (as_seq h0 b) (v bBits - v i - 1);

    let sw1 = bit ^. sw.(0ul) in
    lemma_bit_xor_is_sum_mod2 #a_t bit (LSeq.index (as_seq h2 sw) 0);
    cswap2 len ctx_len k sw1 acc a;

    k.lmul ctx a acc a; // a = (a * acc) % n
    k.lsqr ctx acc acc; // a = (a * a) % n
    sw.(0ul) <- bit
  );
  let sw0 = sw.(0ul) in
  cswap2 len ctx_len k sw0 acc a;
  pop_frame ()


let lexp_pow2 #a_t len ctx_len k ctx a b res =
  copy res a;
  let h0 = ST.get () in
  [@ inline_let]
  let refl1 i : GTot k.to.t_spec = k.to.refl (as_seq h0 res) in

  [@ inline_let]
  let inv h (i:nat{i <= v b}) =
    modifies (loc res) h0 h /\
    k.to.linv (as_seq h res) /\
    k.to.refl (as_seq h res) == Loops.repeat i k.to.concr_ops.SE.sqr (refl1 0) in

  Loops.eq_repeat0 k.to.concr_ops.SE.sqr (refl1 0);
  Lib.Loops.for 0ul b inv
  (fun j ->
    Loops.unfold_repeat (v b) k.to.concr_ops.SE.sqr (refl1 0) (v j);
    k.lsqr ctx res res)


let lexp_pow2_in_place #a_t len ctx_len k ctx acc b =
  let h0 = ST.get () in
  [@ inline_let]
  let refl1 i : GTot k.to.t_spec = k.to.refl (as_seq h0 acc) in

  [@ inline_let]
  let inv h (i:nat{i <= v b}) =
    modifies (loc acc) h0 h /\
    k.to.linv (as_seq h acc) /\
    k.to.refl (as_seq h acc) == Loops.repeat i k.to.concr_ops.SE.sqr (refl1 0) in

  Loops.eq_repeat0 k.to.concr_ops.SE.sqr (refl1 0);
  Lib.Loops.for 0ul b inv
  (fun j ->
    Loops.unfold_repeat (v b) k.to.concr_ops.SE.sqr (refl1 0) (v j);
    k.lsqr ctx acc acc)


//////////////////////////////
//// the precomputed table ///
//////////////////////////////

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

//////////////////////////////////////////////////////////

#set-options "--z3rlimit 100"

inline_for_extraction noextract
val bn_get_bits_l:
    #b_t:inttype_a
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits b_t < v bLen}
  -> b:lbuffer (uint_t b_t SEC) bLen
  -> l:size_t{0 < v l /\ v l < bits b_t}
  -> i:size_t{v i < v bBits / v l} ->
  Stack (uint_t b_t SEC)
  (requires fun h -> live h b /\
    BD.bn_v h b < pow2 (v bBits))
  (ensures  fun h0 r h1 -> h0 == h1 /\
    v r == LE.get_bits_l (v bBits) (BD.bn_v h0 b) (v l) (v i))

let bn_get_bits_l #b_t bLen bBits b l i =
  assert (v (bBits -! bBits %. l) = v bBits - v bBits % v l);
  let bk = bBits -! bBits %. l in
  assert (v bk == v bBits - v bBits % v l);

  Math.Lemmas.lemma_mult_le_left (v l) (v i + 1) (v bBits / v l);
  assert (v l * (v i + 1) <= v bk);
  assert (v (bk -! l *! i -! l) == v bk - v l * v i - v l);

  [@ inline_let]
  let k = bk -! l *! i -! l in
  assert (v k == v bk - v l * v i - v l);
  Math.Lemmas.lemma_div_le (v k) (v bBits - 1) (bits b_t);
  assert (v k / bits b_t < v bLen);

  let h0 = ST.get () in
  SN.bn_get_bits_lemma (as_seq h0 b) (v k) (v l);
  BN.bn_get_bits bLen b k l


inline_for_extraction noextract
val bn_get_bits_c:
    #b_t:inttype_a
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits b_t < v bLen}
  -> b:lbuffer (uint_t b_t SEC) bLen
  -> l:size_t{0 < v l /\ v l < bits b_t /\ 0 < v bBits % v l} ->
  Stack (uint_t b_t SEC)
  (requires fun h -> live h b /\
    BD.bn_v h b < pow2 (v bBits))
  (ensures  fun h0 r h1 -> h0 == h1 /\
    v r == (BD.bn_v h0 b / pow2 (v bBits / v l * v l)) % pow2 (v l))

let bn_get_bits_c #b_t bLen bBits b l =
  let h0 = ST.get () in
  assert (v (bBits /. l *! l) == v bBits / v l * v l);
  [@ inline_let]
  let i = bBits /. l *! l in
  assert (v i == v bBits / v l * v l);
  assert (v i <= v bBits - 1);
  Math.Lemmas.lemma_div_le (v i) (v bBits - 1) (bits b_t);
  assert (v i / bits b_t < v bLen);
  SN.bn_get_bits_lemma (as_seq h0 b) (v i) (v l);
  BN.bn_get_bits bLen b i l


let lprecomp_get_vartime #a_t len ctx_len k a table_len table bits_l tmp =
  let bits_l32 = Lib.RawIntTypes.(size_from_UInt32 (u32_to_UInt32 (to_u32 bits_l))) in
  assert (v bits_l32 == v bits_l /\ v bits_l < v table_len);
  Math.Lemmas.lemma_mult_le_right (v len) (v bits_l + 1) (v table_len);
  assert (v (bits_l32 *! len) == v bits_l32 * v len);

  let h0 = ST.get () in
  let a_bits_l = sub table (bits_l32 *! len) len in
  let h1 = ST.get () in
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h0 table) (v bits_l));
  assert (k.to.refl (as_seq h1 a_bits_l) == SE.pow k.to.concr_ops (k.to.refl (as_seq h0 a)) (v bits_l));
  copy tmp a_bits_l


let lprecomp_get_consttime #a_t len ctx_len k a table_len table bits_l tmp =
  Math.Lemmas.lemma_mult_le_right (v len) (v bits_l + 1) (v table_len);
  let h0 = ST.get () in
  PT.table_select_consttime len table_len table bits_l tmp;
  let h1 = ST.get () in
  assert (as_seq h1 tmp == LSeq.sub (as_seq h0 table) (v bits_l * v len) (v len));
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h0 table) (v bits_l));
  assert (k.to.refl (as_seq h1 tmp) == SE.pow k.to.concr_ops (k.to.refl (as_seq h0 a)) (v bits_l))


inline_for_extraction noextract
let lmul_acc_pow_a_bits_l_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> l:size_t{0 < v l /\ v l < bits a_t /\ v l < 32}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> i:size_t{v i < v bBits / v l}
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\ live h table /\
    disjoint a acc /\ disjoint a ctx /\ disjoint a table /\ disjoint b acc /\
    disjoint acc ctx /\ disjoint acc table /\ disjoint ctx table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    SE.mul_acc_pow_a_bits_l #k.to.t_spec k.to.concr_ops (k.to.refl (as_seq h0 a))
      (v bBits) (BD.bn_v h0 b) (v l) (v i) (k.to.refl (as_seq h0 acc)))


// acc <- acc * a^b_i
inline_for_extraction noextract
val lmul_acc_pow_a_bits_l:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lmul_acc_pow_a_bits_l_st a_t len ctx_len k

let lmul_acc_pow_a_bits_l #a_t len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table i acc =
  push_frame ();
  let bits_l = bn_get_bits_l bLen bBits b l i in
  assert (v bits_l < v table_len);

  let a_bits_l = create len (uint #a_t #SEC 0) in
  lprecomp_get a table_len table bits_l a_bits_l;
  k.lmul ctx acc a_bits_l acc;
  pop_frame ()


inline_for_extraction noextract
let lexp_fw_f_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> l:size_t{0 < v l /\ v l < bits a_t /\ v l < 32}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> i:size_t{v i < v bBits / v l}
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\ live h table /\
    disjoint a acc /\ disjoint a ctx /\ disjoint a table /\ disjoint b acc /\
    disjoint acc ctx /\ disjoint acc table /\ disjoint ctx table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    SE.exp_fw_f #k.to.t_spec k.to.concr_ops (k.to.refl (as_seq h0 a))
      (v bBits) (BD.bn_v h0 b) (v l) (v i) (k.to.refl (as_seq h0 acc)))


// acc <- acc^(2^l) * a^b_i
inline_for_extraction noextract
val lexp_fw_f:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_fw_f_st a_t len ctx_len k

let lexp_fw_f #a_t len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table i acc =
  lexp_pow2_in_place len ctx_len k ctx acc l;
  lmul_acc_pow_a_bits_l #a_t len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table i acc


inline_for_extraction noextract
let lexp_fw_loop_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> l:size_t{0 < v l /\ v l < bits a_t /\ v l < 32}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\ live h table /\
    disjoint a acc /\ disjoint a ctx /\ disjoint a table /\ disjoint b acc /\
    disjoint acc ctx /\ disjoint acc table /\ disjoint ctx table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\ k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    Loops.repeati (v bBits / v l) (SE.exp_fw_f k.to.concr_ops (k.to.refl (as_seq h0 a))
      (v bBits) (BD.bn_v h0 b) (v l)) (k.to.refl (as_seq h0 acc)))


inline_for_extraction noextract
val lexp_fw_loop:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_fw_loop_st a_t len ctx_len k

let lexp_fw_loop #a_t len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table acc =
  let h0 = ST.get () in

  [@ inline_let]
  let refl1 i : GTot k.to.t_spec = k.to.refl (as_seq h0 acc) in
  [@inline_let]
  let spec (h:mem) = SE.exp_fw_f k.to.concr_ops (k.to.refl (as_seq h0 a))
    (v bBits) (BD.bn_v h0 b) (v l) in

  [@inline_let]
  let inv h (i:nat{i <= v bBits / v l}) =
    modifies (loc acc) h0 h /\
    k.to.linv (as_seq h acc) /\
    k.to.refl (as_seq h acc) == Loops.repeati i (spec h0) (refl1 0) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h table) j) in

  Loops.eq_repeati0 (v bBits / v l) (spec h0) (refl1 0);
  Lib.Loops.for 0ul (bBits /. l) inv
  (fun i ->
    Loops.unfold_repeati (v bBits / v l) (spec h0) (refl1 0) (v i);
    lexp_fw_f len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table i acc
  )


inline_for_extraction noextract
let lexp_fw_acc0_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{(v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> l:size_t{0 < v l /\ v l < bits a_t /\ v l < 32}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h -> v bBits % v l <> 0 /\
    live h a /\ live h b /\ live h acc /\ live h ctx /\ live h table /\
    disjoint a acc /\ disjoint a ctx /\ disjoint a table /\ disjoint b acc /\
    disjoint acc ctx /\ disjoint acc table /\ disjoint ctx table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\ k.to.linv (as_seq h a) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    SE.exp_fw_acc0 k.to.concr_ops (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b) (v l))


inline_for_extraction noextract
val lexp_fw_acc0:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_fw_acc0_st a_t len ctx_len k

let lexp_fw_acc0 #a_t len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table acc =
  let h0 = ST.get () in
  assert (v (bBits %. l) == v bBits % v l);
  let bits_c = bn_get_bits_c bLen bBits b l in
  lprecomp_get a table_len table bits_c acc


inline_for_extraction noextract
let lprecomp_get_one_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (k:concrete_ops a_t len ctx_len) =
    a:lbuffer (uint_t a_t SEC) len
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t}
  -> table:lbuffer (uint_t a_t SEC) (table_len *! len)
  -> res:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h table /\ live h res /\
    disjoint a table /\ disjoint a res /\ disjoint table res /\
    k.to.linv (as_seq h a) /\
    (forall (j:nat{j < v table_len}).
      precomp_table_inv len ctx_len k (as_seq h a) table_len (as_seq h table) j))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    k.to.linv (as_seq h1 res) /\
    k.to.refl (as_seq h1 res) == k.to.concr_ops.SE.one ())


inline_for_extraction noextract
val lprecomp_get_one:
     #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len ->
  lprecomp_get_one_st a_t len ctx_len k

let lprecomp_get_one #a_t len ctx_len k a table_len table res =
  let h0 = ST.get () in
  copy res (sub table 0ul len);
  let h1 = ST.get () in
  assert (precomp_table_inv len ctx_len k (as_seq h0 a) table_len (as_seq h0 table) 0);
  assert (k.to.refl (as_seq h1 res) == SE.pow k.to.concr_ops (k.to.refl (as_seq h0 a)) 0);
  SE.pow_eq0 k.to.concr_ops (k.to.refl (as_seq h0 a))


inline_for_extraction noextract
val lexp_fw_table_gen:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_fw_table_st a_t len ctx_len k

let lexp_fw_table_gen #a_t len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table acc =
  assert (v (bBits %. l) = v bBits % v l);
  if bBits %. l <> 0ul then
    lexp_fw_acc0 len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table acc
  else lprecomp_get_one len ctx_len k a table_len table acc;
  lexp_fw_loop #a_t len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table acc


let lexp_fw_table_vartime #a_t len ctx_len k ctx a bLen bBits b l table_len table acc =
  lexp_fw_table_gen #a_t len ctx_len k
    (lprecomp_get_vartime #a_t len ctx_len k)
    ctx a bLen bBits b l table_len table acc


let lexp_fw_table_consttime #a_t len ctx_len k ctx a bLen bBits b l table_len table acc =
  lexp_fw_table_gen #a_t len ctx_len k
    (lprecomp_get_consttime #a_t len ctx_len k)
    ctx a bLen bBits b l table_len table acc


inline_for_extraction noextract
val lexp_fw_gen:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> lprecomp_get:lprecomp_get_st a_t len ctx_len k ->
  lexp_fw_st a_t len ctx_len k

let lexp_fw_gen #a_t len ctx_len k lprecomp_get ctx a bLen bBits b acc l =
  push_frame ();
  Math.Lemmas.pow2_lt_compat 32 (v l);
  [@inline_let]
  let table_len = 1ul <<. l in
  assert (v table_len == pow2 (v l));
  Math.Lemmas.pow2_le_compat (v l) 1;
  assert (1 < v table_len /\ v table_len * v len <= max_size_t);

  let table = create (table_len *! len) (uint #a_t #SEC 0) in
  lprecomp_table #a_t len ctx_len k ctx a table_len table;
  lexp_fw_table_gen #a_t len ctx_len k lprecomp_get ctx a bLen bBits b l table_len table acc;
  pop_frame ()


let lexp_fw_vartime #a_t len ctx_len k ctx a bLen bBits b acc l =
  lexp_fw_gen #a_t len ctx_len k
    (lprecomp_get_vartime #a_t len ctx_len k)
    ctx a bLen bBits b acc l


let lexp_fw_consttime #a_t len ctx_len k ctx a bLen bBits b acc l =
  lexp_fw_gen #a_t len ctx_len k
    (lprecomp_get_consttime #a_t len ctx_len k)
    ctx a bLen bBits b acc l
