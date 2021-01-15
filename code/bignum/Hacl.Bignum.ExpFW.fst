module Hacl.Bignum.ExpFW

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators
module B = LowStar.Buffer

module S = Hacl.Spec.Bignum.ExpFW
module SN = Hacl.Spec.Bignum
module SM = Hacl.Spec.Bignum.Montgomery
module BB = Hacl.Spec.Bignum.Base

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module PT = Hacl.Bignum.PrecompTable

friend Hacl.Spec.Bignum.ExpFW

#reset-options "--z3rlimit 150 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mod_exp_pow2_mont_in_place_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> b:size_t
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h res /\ disjoint n res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_exp_pow2_mont (as_seq h0 n) mu (as_seq h0 res) (v b))


inline_for_extraction noextract
val bn_mod_exp_pow2_mont_in_place: #t:limb_t -> k:BM.mont t -> bn_mod_exp_pow2_mont_in_place_st t k.BM.bn.BN.len
let bn_mod_exp_pow2_mont_in_place #t k n mu b res =
  let h0 = ST.get () in
  [@ inline_let]
  let refl h i = as_seq h res in
  [@ inline_let]
  let spec h0 = SM.bn_mont_sqr (as_seq h0 n) mu in

  [@ inline_let]
  let inv h (i:nat{i <= v b}) =
    modifies1 res h0 h /\
    live h res /\ live h n /\ disjoint n res /\
    refl h i == Loops.repeat i (spec h0) (refl h0 0) in

  Loops.eq_repeat0 (spec h0) (refl h0 0);
  Lib.Loops.for 0ul b inv
  (fun j ->
    Loops.unfold_repeat (v b) (spec h0) (refl h0 0) (v j);
    k.BM.sqr n mu res res)


inline_for_extraction noextract
val bn_get_bits_l:
    #t:limb_t
  -> bBits:size_t{0 < v bBits}
  -> bLen:size_t{bLen == blocks bBits (size (bits t))}
  -> b:lbignum t bLen
  -> l:size_t{0 < v l /\ v l < bits t}
  -> i:size_t{v i < v bBits / v l} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ v r < pow2 (v l) /\
    r == S.bn_get_bits_l (v bBits) (v bLen) (as_seq h0 b) (v l) (v i))

let bn_get_bits_l #t bBits bLen b l i =
  Math.Lemmas.lemma_mult_le_left (v l) (v i + 1) (v bBits / v l);
  assert (v l * (v i + 1) <= v l * (v bBits / v l));
  Math.Lemmas.multiply_fractions (v bBits) (v l);
  assert (v l * (v i + 1) <= v bBits);
  let h0 = ST.get () in
  SN.bn_get_bits_lemma (as_seq h0 b) (v bBits - v l * v i - v l) (v l);
  BN.bn_get_bits bLen b (bBits -! l *! i -! l) l


inline_for_extraction noextract
let bn_mod_exp_fw_mont_f_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> bBits:size_t{0 < v bBits}
  -> bLen:size_t{bLen == blocks bBits (size (bits t))}
  -> b:lbignum t bLen
  -> l:size_t{0 < v l /\ v l < bits t}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table:lbignum t (table_len *! len)
  -> i:size_t{v i < v bBits / v l}
  -> accM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h table /\ live h accM /\
    disjoint accM table /\ disjoint accM b /\ disjoint accM n /\
    disjoint accM n /\ disjoint accM b)
  (ensures  fun h0 _ h1 -> modifies (loc accM) h0 h1 /\
    as_seq h1 accM == S.bn_mod_exp_fw_mont_f (as_seq h0 n) mu (v bBits) (v bLen) (as_seq h0 b)
      (v l) (v table_len) (as_seq h0 table) (v i) (as_seq h0 accM))


inline_for_extraction noextract
val bn_mod_exp_fw_mont_ct_f: #t:limb_t -> k:BM.mont t -> bn_mod_exp_fw_mont_f_st t k.BM.bn.BN.len
let bn_mod_exp_fw_mont_ct_f #t k n mu bBits bLen b l table_len table i accM =
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let bits_l = bn_get_bits_l bBits bLen b l i in
  assert (v bits_l < v table_len);

  let a_powbits_l = create len (uint #t #SEC 0) in
  Math.Lemmas.lemma_mult_le_right (v len) (v bits_l + 1) (v table_len);
  PT.table_select_ct len table_len table bits_l a_powbits_l;

  bn_mod_exp_pow2_mont_in_place k n mu l accM;
  k.BM.mul n mu accM a_powbits_l accM;
  pop_frame ()


inline_for_extraction noextract
val bn_mod_exp_fw_mont_raw_f: #t:limb_t -> k:BM.mont t -> bn_mod_exp_fw_mont_f_st t k.BM.bn.BN.len
let bn_mod_exp_fw_mont_raw_f #t k n mu bBits bLen b l table_len table i accM =
  [@inline_let] let len = k.BM.bn.BN.len in

  let bits_l = bn_get_bits_l bBits bLen b l i in
  let bits_l32 = Lib.RawIntTypes.(size_from_UInt32 (u32_to_UInt32 (to_u32 bits_l))) in
  assert (v bits_l32 == v bits_l);

  Math.Lemmas.lemma_mult_le_right (v len) (v bits_l32 + 1) (v table_len);
  let a_powbits_l = sub table (bits_l32 *! len) len in

  bn_mod_exp_pow2_mont_in_place k n mu l accM;
  k.BM.mul n mu accM a_powbits_l accM


inline_for_extraction noextract
val bn_get_bits_c:
    #t:limb_t
  -> bBits:size_t{0 < v bBits}
  -> bLen:size_t{bLen == blocks bBits (size (bits t))}
  -> b:lbignum t bLen
  -> l:size_t{0 < v l /\ v l < bits t} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ v r < pow2 (v l) /\
    r == S.bn_get_bits_c (v bBits) (v bLen) (as_seq h0 b) (v l))

let bn_get_bits_c #t bBits bLen b l =
  let c = bBits %. l in
  assert (v c == v bBits % v l);
  let bits_c = BN.bn_get_bits bLen b 0ul c in
  let h0 = ST.get () in
  SN.bn_get_bits_lemma (as_seq h0 b) 0 (v c);
  Math.Lemmas.pow2_lt_compat (v l) (v c);
  assert (v bits_c < pow2 (v c));
  bits_c


inline_for_extraction noextract
let bn_mod_exp_fw_mont_rem_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> bBits:size_t{0 < v bBits}
  -> bLen:size_t{bLen == blocks bBits (size (bits t))}
  -> b:lbignum t bLen
  -> l:size_t{0 < v l /\ v l < bits t}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table:lbignum t (table_len *! len)
  -> accM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h table /\ live h accM /\
    disjoint accM table /\ disjoint accM b /\ disjoint accM n /\
    disjoint accM n /\ disjoint accM b)
  (ensures  fun h0 _ h1 -> modifies (loc accM) h0 h1 /\
    as_seq h1 accM == S.bn_mod_exp_fw_mont_rem (as_seq h0 n) mu (v bBits) (v bLen) (as_seq h0 b)
      (v l) (v table_len) (as_seq h0 table) (as_seq h0 accM))


inline_for_extraction noextract
val bn_mod_exp_fw_mont_rem_ct: #t:limb_t -> k:BM.mont t -> bn_mod_exp_fw_mont_rem_st t k.BM.bn.BN.len
let bn_mod_exp_fw_mont_rem_ct #t k n mu bBits bLen b l table_len table accM =
  push_frame ();
  let c = bBits %. l in
  assert (v c == v bBits % v l);
  bn_mod_exp_pow2_mont_in_place k n mu c accM;
  let bits_c = bn_get_bits_c #t bBits bLen b l in
  assert (v bits_c < v table_len);

  [@inline_let] let len = k.BM.bn.BN.len in
  let a_powbits_c = create len (uint #t #SEC 0) in
  Math.Lemmas.lemma_mult_le_right (v len) (v bits_c + 1) (v table_len);
  PT.table_select_ct len table_len table bits_c a_powbits_c;
  k.BM.mul n mu accM a_powbits_c accM;
  pop_frame ()


inline_for_extraction noextract
val bn_mod_exp_fw_mont_rem_raw: #t:limb_t -> k:BM.mont t -> bn_mod_exp_fw_mont_rem_st t k.BM.bn.BN.len
let bn_mod_exp_fw_mont_rem_raw #t k n mu bBits bLen b l table_len table accM =
  let c = bBits %. l in
  assert (v c == v bBits % v l);
  bn_mod_exp_pow2_mont_in_place k n mu c accM;
  let bits_c = bn_get_bits_c #t bBits bLen b l in
  assert (v bits_c < v table_len);
  let bits_c32 = Lib.RawIntTypes.(size_from_UInt32 (u32_to_UInt32 (to_u32 bits_c))) in
  assert (v bits_c32 == v bits_c);

  [@inline_let] let len = k.BM.bn.BN.len in
  Math.Lemmas.lemma_mult_le_right (v len) (v bits_c32 + 1) (v table_len);
  let a_powbits_l = sub table (bits_c32 *! len) len in
  k.BM.mul n mu accM a_powbits_l accM


inline_for_extraction noextract
let bn_mod_exp_fw_mont_loop_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> bBits:size_t{0 < v bBits}
  -> bLen:size_t{bLen == blocks bBits (size (bits t))}
  -> b:lbignum t bLen
  -> l:size_t{0 < v l /\ v l < bits t /\ pow2 (v l) * v len <= max_size_t}
  -> table_len:size_t{1 < v table_len /\ v table_len * v len <= max_size_t /\ v table_len == pow2 (v l)}
  -> table:lbignum t (table_len *! len)
  -> accM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h accM /\ live h table /\
    disjoint accM b /\ disjoint accM n /\ disjoint accM table /\ disjoint n table)
  (ensures  fun h0 _ h1 -> modifies (loc accM) h0 h1 /\
   (Math.Lemmas.multiply_fractions (v bBits) (v l);
    as_seq h1 accM ==
    Loops.repeati (v bBits / v l) (S.bn_mod_exp_fw_mont_f (as_seq h0 n) mu
      (v bBits) (v bLen) (as_seq h0 b) (v l) (v table_len) (as_seq h0 table)) (as_seq h0 accM)))


inline_for_extraction noextract
val bn_mod_exp_fw_mont_loop:
    #t:limb_t
  -> k:BM.mont t
  -> bn_mod_exp_fw_mont_f: bn_mod_exp_fw_mont_f_st t k.BM.bn.BN.len ->
  bn_mod_exp_fw_mont_loop_st t k.BM.bn.BN.len

let bn_mod_exp_fw_mont_loop #t k bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len table accM =
  Math.Lemmas.multiply_fractions (v bBits) (v l);
  let it = bBits /. l in
  assert (v it == v bBits / v l);

  [@inline_let]
  let spec h0 = S.bn_mod_exp_fw_mont_f (as_seq h0 n) mu
      (v bBits) (v bLen) (as_seq h0 b) (v l) (v table_len) (as_seq h0 table) in
  let h0 = ST.get () in

  loop1 h0 it accM spec
  (fun i ->
    Loops.unfold_repeati (v it) (spec h0) (as_seq h0 accM) (v i);
    bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len table i accM
  )


inline_for_extraction noextract
let bn_mod_exp_fw_mont_aux_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> bBits:size_t{0 < v bBits}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> l:size_t{0 < v l /\ v l < bits U32 /\ pow2 (v l) * v len <= max_size_t}
  -> r2:lbignum t len
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h aM /\ live h resM /\ live h r2 /\
    disjoint resM aM /\ disjoint resM b /\ disjoint resM n /\
    disjoint resM r2 /\ disjoint aM n /\
    disjoint aM b /\ disjoint aM r2 /\ disjoint n r2)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.bn_mod_exp_fw_mont_ (as_seq h0 n) mu (as_seq h0 aM) (v bBits) (as_seq h0 b) (v l) (as_seq h0 r2))


inline_for_extraction noextract
val bn_mod_exp_fw_mont_aux:
    #t:limb_t
  -> k:BM.mont t
  -> bn_mod_exp_fw_mont_f: bn_mod_exp_fw_mont_f_st t k.BM.bn.BN.len
  -> bn_mod_exp_fw_mont_rem: bn_mod_exp_fw_mont_rem_st t k.BM.bn.BN.len ->
  bn_mod_exp_fw_mont_aux_st t k.BM.bn.BN.len

let bn_mod_exp_fw_mont_aux #t k bn_mod_exp_fw_mont_f bn_mod_exp_fw_mont_rem n mu aM bBits b l r2 accM =
  [@inline_let] let len = k.BM.bn.BN.len in
  let bLen = blocks bBits (size (bits t)) in
  push_frame ();
  BM.bn_mont_one k n mu r2 accM;

  let table_len = 1ul <<. l in
  assert (v table_len == pow2 (v l));
  Math.Lemmas.pow2_le_compat (v l) 1;
  assert (1 < v table_len /\ v table_len * v len <= max_size_t);
  let table = create (table_len *! len) (uint #t #SEC 0) in
  PT.bn_mod_precomp_table_mont k n mu table_len aM accM table;

  bn_mod_exp_fw_mont_loop #t k bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len table accM;

  assert (v (bBits %. l) == v bBits % v l);
  if bBits %. l <>. 0ul then
    bn_mod_exp_fw_mont_rem n mu bBits bLen b l table_len table accM;
  pop_frame()


inline_for_extraction noextract
val bn_mod_exp_fw_precompr2_:
    #t:limb_t
  -> k:BM.mont t
  -> bn_mod_exp_fw_mont_f: bn_mod_exp_fw_mont_f_st t k.BM.bn.BN.len
  -> bn_mod_exp_fw_mont_rem: bn_mod_exp_fw_mont_rem_st t k.BM.bn.BN.len ->
  bn_mod_exp_fw_precompr2_st t k.BM.bn.BN.len

let bn_mod_exp_fw_precompr2_ #t k bn_mod_exp_fw_mont_f bn_mod_exp_fw_mont_rem n a bBits b l r2 res =
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let mu = BM.mod_inv_limb n.(0ul) in
  let aM = create len (uint #t #SEC 0) in
  k.BM.to n mu r2 a aM;

  let resM = create len (uint #t #SEC 0) in
  bn_mod_exp_fw_mont_aux #t k bn_mod_exp_fw_mont_f bn_mod_exp_fw_mont_rem n mu aM bBits b l r2 resM;
  k.BM.from n mu resM res;
  pop_frame ()


let bn_mod_exp_fw_raw_precompr2 #t k n a bBits b l r2 res =
  bn_mod_exp_fw_precompr2_ #t k
    (bn_mod_exp_fw_mont_raw_f k) (bn_mod_exp_fw_mont_rem_raw k) n a bBits b l r2 res


let bn_mod_exp_fw_ct_precompr2 #t k n a bBits b l r2 res =
  bn_mod_exp_fw_precompr2_ #t k
    (bn_mod_exp_fw_mont_ct_f k) (bn_mod_exp_fw_mont_rem_ct k) n a bBits b l r2 res
