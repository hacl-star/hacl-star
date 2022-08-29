module Hacl.Impl.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module S = Lib.Exponentiation

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
  let refl1 i : GTot (k.to.a_spec & k.to.a_spec) =
    (refl (as_seq h0 acc), refl (as_seq h0 a)) in

  [@inline_let]
  let spec (h:mem) = S.exp_rl_f k.to.comm_monoid (v bBits) (BD.bn_v h0 b) in

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
    S.cswap (v bit) (k.to.refl (as_seq h0 p1)) (k.to.refl (as_seq h0 p2)))

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
  let refl1 i : GTot (k.to.a_spec & k.to.a_spec & nat) =
    (k.to.refl (as_seq h0 acc), k.to.refl (as_seq h0 a), v (LSeq.index (as_seq h0 sw) 0)) in

  [@inline_let]
  let spec (h:mem) = S.exp_mont_ladder_swap_f k.to.comm_monoid (v bBits) (BD.bn_v h0 b) in

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
  let refl1 i : GTot k.to.a_spec = k.to.refl (as_seq h0 res) in
  [@ inline_let]
  let spec h0 = S.sqr k.to.comm_monoid in

  [@ inline_let]
  let inv h (i:nat{i <= v b}) =
    modifies (loc res) h0 h /\
    k.to.linv (as_seq h res) /\
    k.to.refl (as_seq h res) == Loops.repeat i (spec h0) (refl1 0) in

  Loops.eq_repeat0 (spec h0) (refl1 0);
  Lib.Loops.for 0ul b inv
  (fun j ->
    Loops.unfold_repeat (v b) (spec h0) (refl1 0) (v j);
    k.lsqr ctx res res)


let lexp_pow2_in_place #a_t len ctx_len k ctx acc b =
  let h0 = ST.get () in
  [@ inline_let]
  let refl1 i : GTot k.to.a_spec = k.to.refl (as_seq h0 acc) in
  [@ inline_let]
  let spec h0 = S.sqr k.to.comm_monoid in

  [@ inline_let]
  let inv h (i:nat{i <= v b}) =
    modifies (loc acc) h0 h /\
    k.to.linv (as_seq h acc) /\
    k.to.refl (as_seq h acc) == Loops.repeat i (spec h0) (refl1 0) in

  Loops.eq_repeat0 (spec h0) (refl1 0);
  Lib.Loops.for 0ul b inv
  (fun j ->
    Loops.unfold_repeat (v b) (spec h0) (refl1 0) (v j);
    k.lsqr ctx acc acc)

//---------------------------------------------------

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
    v r == S.get_bits_l (v bBits) (BD.bn_v h0 b) (v l) (v i))

let bn_get_bits_l #b_t bLen bBits b l i =
  assert (v (bBits -! bBits %. l) = v bBits - v bBits % v l);
  let bk = bBits -! bBits %. l in
  assert (v bk == v bBits - v bBits % v l);

  Math.Lemmas.lemma_mult_le_left (v l) (v i + 1) (v bBits / v l);
  assert (v l * (v i + 1) <= v bk);
  Math.Lemmas.distributivity_add_right (v l) (v i) 1;
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

//---------------------------------------------------

inline_for_extraction noextract
let lmul_acc_pow_a_bits_l_st
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
  -> i:size_t{v i < v bBits / v l}
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\ live h table /\
    disjoint a acc /\ disjoint a ctx /\ disjoint b acc /\
    disjoint acc ctx /\ disjoint acc table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    table_inv (as_seq h a) (as_seq h table))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.mul_acc_pow_a_bits_l #k.to.a_spec k.to.comm_monoid (k.to.refl (as_seq h0 a))
      (v bBits) (BD.bn_v h0 b) (v l) (v i) (k.to.refl (as_seq h0 acc)))


// acc <- acc * a^b_i
inline_for_extraction noextract
val lmul_acc_pow_a_bits_l:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len
  -> table_inv:table_inv_t a_t len table_len
  -> pow_a_to_small_b:pow_a_to_small_b_st a_t len ctx_len k l table_len table_inv ->
  lmul_acc_pow_a_bits_l_st a_t len ctx_len k l table_len table_inv

let lmul_acc_pow_a_bits_l #a_t len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table i acc =
  let h0 = ST.get () in
  push_frame ();
  let bits_l = bn_get_bits_l bLen bBits b l i in
  assert (v bits_l < pow2 (v l));

  let a_bits_l = create len (uint #a_t #SEC 0) in
  pow_a_to_small_b ctx (as_seq h0 a) table bits_l a_bits_l;
  k.lmul ctx acc a_bits_l acc;
  pop_frame ()


inline_for_extraction noextract
let lexp_fw_f_st
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
  -> i:size_t{v i < v bBits / v l}
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\ live h table /\
    disjoint a acc /\ disjoint a ctx /\ disjoint b acc /\
    disjoint acc ctx /\ disjoint acc table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    table_inv (as_seq h a) (as_seq h table))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.exp_fw_f #k.to.a_spec k.to.comm_monoid (k.to.refl (as_seq h0 a))
      (v bBits) (BD.bn_v h0 b) (v l) (v i) (k.to.refl (as_seq h0 acc)))


// acc <- acc^(2^l) * a^b_i
inline_for_extraction noextract
val lexp_fw_f:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len
  -> table_inv:table_inv_t a_t len table_len
  -> pow_a_to_small_b:pow_a_to_small_b_st a_t len ctx_len k l table_len table_inv ->
  lexp_fw_f_st a_t len ctx_len k l table_len table_inv

let lexp_fw_f #a_t len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table i acc =
  lexp_pow2_in_place len ctx_len k ctx acc l;
  lmul_acc_pow_a_bits_l #a_t len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table i acc


inline_for_extraction noextract
let lexp_fw_loop_st
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
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\ live h table /\
    disjoint a acc /\ disjoint a ctx /\ disjoint b acc /\
    disjoint acc ctx /\ disjoint acc table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    table_inv (as_seq h a) (as_seq h table))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\ k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    Loops.repeati (v bBits / v l) (S.exp_fw_f k.to.comm_monoid (k.to.refl (as_seq h0 a))
      (v bBits) (BD.bn_v h0 b) (v l)) (k.to.refl (as_seq h0 acc)))


inline_for_extraction noextract
val lexp_fw_loop:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len
  -> table_inv:table_inv_t a_t len table_len
  -> pow_a_to_small_b:pow_a_to_small_b_st a_t len ctx_len k l table_len table_inv ->
  lexp_fw_loop_st a_t len ctx_len k l table_len table_inv

let lexp_fw_loop #a_t len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table acc =
  let h0 = ST.get () in

  [@ inline_let]
  let refl1 i : GTot k.to.a_spec = k.to.refl (as_seq h0 acc) in
  [@inline_let]
  let spec (h:mem) = S.exp_fw_f k.to.comm_monoid (k.to.refl (as_seq h0 a))
    (v bBits) (BD.bn_v h0 b) (v l) in

  [@inline_let]
  let inv h (i:nat{i <= v bBits / v l}) =
    modifies (loc acc) h0 h /\
    k.to.linv (as_seq h acc) /\
    k.to.refl (as_seq h acc) == Loops.repeati i (spec h0) (refl1 0) /\
    table_inv (as_seq h a) (as_seq h table) in

  Loops.eq_repeati0 (v bBits / v l) (spec h0) (refl1 0);
  Lib.Loops.for 0ul (bBits /. l) inv
  (fun i ->
    Loops.unfold_repeati (v bBits / v l) (spec h0) (refl1 0) (v i);
    lexp_fw_f len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table i acc
  )


inline_for_extraction noextract
let lexp_fw_acc0_st
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
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h -> v bBits % v l <> 0 /\
    live h a /\ live h b /\ live h acc /\ live h ctx /\ live h table /\
    disjoint a acc /\ disjoint a ctx /\ disjoint b acc /\
    disjoint acc ctx /\ disjoint acc table /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\ k.to.linv (as_seq h a) /\
    table_inv (as_seq h a) (as_seq h table))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.exp_fw_acc0 k.to.comm_monoid (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b) (v l))


inline_for_extraction noextract
val lexp_fw_acc0:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len
  -> table_inv:table_inv_t a_t len table_len
  -> pow_a_to_small_b:pow_a_to_small_b_st a_t len ctx_len k l table_len table_inv ->
  lexp_fw_acc0_st a_t len ctx_len k l table_len table_inv

let lexp_fw_acc0 #a_t len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table acc =
  let h0 = ST.get () in
  assert (v (bBits %. l) == v bBits % v l);
  let bits_c = bn_get_bits_c bLen bBits b l in
  pow_a_to_small_b ctx (as_seq h0 a) table bits_c acc


let mk_lexp_fw_table #a_t len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table res =
  assert (v (bBits %. l) = v bBits % v l);
  if bBits %. l <> 0ul then
    lexp_fw_acc0 len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table res
  else k.lone ctx res;
  lexp_fw_loop len ctx_len k l table_len table_inv pow_a_to_small_b ctx a bLen bBits b table res

//-------------------------------------

let lprecomp_get_vartime #a_t len ctx_len k l table_len ctx a table bits_l tmp =
  PT.lprecomp_get_vartime #a_t len ctx_len k a table_len table bits_l tmp


let lprecomp_get_consttime #a_t len ctx_len k l table_len ctx a table bits_l tmp =
  PT.lprecomp_get_consttime #a_t len ctx_len k a table_len table bits_l tmp


val lemma_pow2_is_divisible_by_2: l:pos -> Lemma (pow2 l % 2 = 0)
let lemma_pow2_is_divisible_by_2 l =
  Math.Lemmas.pow2_plus 1 (l - 1);
  assert_norm (pow2 1 = 2);
  assert (pow2 l = 2 * pow2 (l - 1));
  Math.Lemmas.lemma_mod_mul_distr_l 2 (pow2 (l - 1)) 2


inline_for_extraction noextract
val lexp_fw_gen:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:concrete_ops a_t len ctx_len
  -> l:size_window_t a_t len
  -> table_len:table_len_t len{1 < v table_len /\ v table_len == pow2 (v l)}
  -> lprecomp_get:pow_a_to_small_b_st a_t len ctx_len k l table_len
                   (table_inv_precomp len ctx_len k l table_len) ->
  lexp_fw_st a_t len ctx_len k l

let lexp_fw_gen #a_t len ctx_len k l table_len lprecomp_get ctx a bLen bBits b res =
  push_frame ();
  Math.Lemmas.pow2_lt_compat 32 (v l);
  lemma_pow2_is_divisible_by_2 (v l);

  let table = create (table_len *! len) (uint #a_t #SEC 0) in
  PT.lprecomp_table #a_t len ctx_len k ctx a table_len table;

  mk_lexp_fw_table len ctx_len k l table_len
    (table_inv_precomp len ctx_len k l table_len)
    lprecomp_get ctx a bLen bBits b table res;
  pop_frame ()


let lexp_fw_vartime #a_t len ctx_len k l ctx a bLen bBits b acc =
  [@inline_let]
  let table_len = 1ul <<. l in
  assert (v table_len == pow2 (v l));
  Math.Lemmas.pow2_le_compat (v l) 1;
  assert (1 < v table_len /\ v table_len * v len <= max_size_t);

  lexp_fw_gen #a_t len ctx_len k l table_len
    (lprecomp_get_vartime len ctx_len k l table_len)
    ctx a bLen bBits b acc


let lexp_fw_consttime #a_t len ctx_len k l ctx a bLen bBits b acc =
  [@inline_let]
  let table_len = 1ul <<. l in
  assert (v table_len == pow2 (v l));
  Math.Lemmas.pow2_le_compat (v l) 1;
  assert (1 < v table_len /\ v table_len * v len <= max_size_t);

  lexp_fw_gen #a_t len ctx_len k l table_len
    (lprecomp_get_consttime len ctx_len k l table_len)
    ctx a bLen bBits b acc
