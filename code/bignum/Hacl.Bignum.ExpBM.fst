module Hacl.Bignum.ExpBM

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module S = Hacl.Spec.Bignum.ExpBM
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

friend Hacl.Spec.Bignum.ExpBM


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_check_mod_exp #t k n a bBits b =
  [@inline_let] let len = k.BM.bn.BN.len in
  let m0 = k.BM.mont_check n in
  let bLen = blocks bBits (size (bits t)) in
  let m1 = BN.bn_is_zero_mask bLen b in
  let m1' = lognot m1 in
  let m2 =
    if bBits <. size (bits t) *! bLen
    then BN.bn_lt_pow2_mask bLen b bBits
    else ones t SEC in
  let m3 = BN.bn_lt_mask len a n in
  let m = m1' &. m2 &. m3 in
  m0 &. m


inline_for_extraction noextract
let bn_mod_exp_raw_loop_st (t:limb_t) (nLen:BN.meta_len t) =
    n:lbignum t nLen
  -> nInv:limb t
  -> bBits:size_t{v bBits > 0}
  -> bLen:size_t{v bLen = v (blocks bBits (size (bits t))) /\ (v bBits - 1) / bits t < v bLen}
  -> b:lbignum t bLen
  -> aM:lbignum t nLen
  -> accM:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h aM /\ live h accM /\
    disjoint aM accM /\ disjoint aM b /\ disjoint aM n /\
    disjoint accM b /\ disjoint accM n)
  (ensures  fun h0 _ h1 -> modifies (loc aM |+| loc accM) h0 h1 /\
    (as_seq h1 aM, as_seq h1 accM) ==
      Loops.repeati (v bBits)
	(S.bn_mod_exp_raw_f (as_seq h0 n) nInv (v bBits) (v bLen) (as_seq h0 b))
      (as_seq h0 aM, as_seq h0 accM))


inline_for_extraction noextract
val bn_mod_exp_raw_loop: #t:limb_t -> k:BM.mont t -> bn_mod_exp_raw_loop_st t k.BM.bn.BN.len
let bn_mod_exp_raw_loop #t k n nInv bBits bLen b aM accM =
  [@inline_let]
  let spec h0 = S.bn_mod_exp_raw_f (as_seq h0 n) nInv (v bBits) (v bLen) (as_seq h0 b) in
  let h0 = ST.get () in
  loop2 h0 bBits aM accM spec
  (fun i ->
    Loops.unfold_repeati (v bBits) (spec h0) (as_seq h0 aM, as_seq h0 accM) (v i);
    let get_bit = BN.bn_get_ith_bit bLen b i in

    if not (Hacl.Bignum.Base.unsafe_bool_of_limb0 get_bit) then
      BM.mul n nInv aM accM accM; // acc = (acc * a) % n
    BM.sqr n nInv aM aM // a = (a * a) % n
  )


let bn_mod_exp_raw_precompr2 #t k n a bBits b r2 res =
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let bLen = blocks bBits (size (bits t)) in
  let nInv = BM.mod_inv_limb n.(0ul) in // n * nInv = 1 (mod (pow2 64))

  let aM   = create len (uint #t #SEC 0) in
  let accM = create len (uint #t #SEC 0) in
  BM.to n nInv r2 a aM;
  BM.bn_mont_one k n nInv r2 accM;
  bn_mod_exp_raw_loop k n nInv bBits bLen b aM accM;
  BM.from n nInv accM res;
  pop_frame ()

///
///  Montgomery ladder for exponentiation
///

inline_for_extraction noextract
let bn_mod_exp_ct_loop_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> nInv:limb t
  -> bBits:size_t{v bBits > 0}
  -> bLen:size_t{v bLen = v (blocks bBits (size (bits t))) /\ (v bBits - 1) / bits t < v bLen}
  -> b:lbignum t bLen
  -> rM0:lbignum t len
  -> rM1:lbignum t len
  -> sw:lbignum t 1ul ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h rM0 /\ live h rM1 /\ live h sw /\
    disjoint rM0 rM1 /\ disjoint rM0 b /\ disjoint rM0 n /\
    disjoint rM1 b /\ disjoint rM1 n /\
    disjoint sw rM0 /\ disjoint sw rM1 /\ disjoint sw b /\ disjoint sw n)
  (ensures  fun h0 _ h1 -> modifies (loc rM0 |+| loc rM1 |+| loc sw) h0 h1 /\
    (as_seq h1 rM0, as_seq h1 rM1, LSeq.index (as_seq h1 sw) 0) ==
      Loops.repeat_gen (v bBits) (S.bn_mod_exp_ct_t t (v len) (v bBits))
	(S.bn_mod_exp_ct_f (as_seq h0 n) nInv (v bBits) (v bLen) (as_seq h0 b))
      (as_seq h0 rM0, as_seq h0 rM1, LSeq.index (as_seq h0 sw) 0))


inline_for_extraction noextract
val bn_mod_exp_ct_loop: #t:limb_t -> k:BM.mont t -> bn_mod_exp_ct_loop_st t k.BM.bn.BN.len
let bn_mod_exp_ct_loop #t k n nInv bBits bLen b rM0 rM1 sw =
  [@inline_let] let len = k.BM.bn.BN.len in
  [@inline_let]
  let refl h i : GTot (S.bn_mod_exp_ct_t t (v len) (v bBits) i) =
    (as_seq h rM0, as_seq h rM1, LSeq.index (as_seq h sw) 0) in
  [@inline_let]
  let footprint i = loc rM0 |+| loc rM1 |+| loc sw in
  [@inline_let]
  let spec h0 = S.bn_mod_exp_ct_f (as_seq h0 n) nInv (v bBits) (v bLen) (as_seq h0 b) in
  let h0 = ST.get () in
  loop h0 bBits (S.bn_mod_exp_ct_t t (v len) (v bBits)) refl footprint spec
  (fun i ->
    Loops.unfold_repeat_gen (v bBits)
      (S.bn_mod_exp_ct_t t (v len) (v bBits)) (spec h0) (refl h0 0) (v i);
    let bit = BN.bn_get_ith_bit bLen b (bBits -! i -! 1ul) in
    let sw1 = bit ^. sw.(0ul) in
    BN.cswap2 len sw1 rM0 rM1;
    BM.mul n nInv rM1 rM0 rM1;
    BM.sqr n nInv rM0 rM0;
    sw.(0ul) <- bit
  );
  let h1 = ST.get () in
  assert (refl h1 (v bBits) == Loops.repeat_gen (v bBits)
    (S.bn_mod_exp_ct_t t (v len) (v bBits)) (spec h0) (refl h0 0))


let bn_mod_exp_ct_precompr2 #t k n a bBits b r2 res =
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let bLen = blocks bBits (size (bits t)) in
  let nInv = BM.mod_inv_limb n.(0ul) in // n * nInv = 1 (mod (pow2 64))

  let rM0 = create len (uint #t #SEC 0) in
  let rM1 = create len (uint #t #SEC 0) in
  let sw  = create 1ul (uint #t #SEC 0) in
  BM.bn_mont_one k n nInv r2 rM0;
  BM.to n nInv r2 a rM1;

  bn_mod_exp_ct_loop k n nInv bBits bLen b rM0 rM1 sw;
  BN.cswap2 len sw.(0ul) rM0 rM1;
  BM.from n nInv rM0 res;
  pop_frame ()
