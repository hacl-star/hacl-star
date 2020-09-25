module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Bignum.Exponentiation
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators
module BD = Hacl.Spec.Bignum.Definitions

friend Hacl.Spec.Bignum.Exponentiation


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
val mk_check_mod_exp:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> check_mod_exp_st t nLen

let mk_check_mod_exp #t nLen #k n a bBits b =
  let m0 = k.BM.check n in
  let bLen = blocks bBits (size (bits t)) in
  let m1 = BN.bn_is_zero_mask bLen b in
  let m1' = lognot m1 in
  let m2 = if bBits <. size (bits t) *! bLen then BN.bn_lt_pow2_mask bLen b bBits else ones t SEC in
  let m3 = BN.bn_lt_mask nLen a n in
  let m = m1' &. m2 &. m3 in
  m0 &. m


[@CInline]
let check_mod_exp #t nLen =
  mk_check_mod_exp nLen #(BM.mk_runtime_mont t nLen)


inline_for_extraction noextract
let bn_mod_exp_loop_st (t:limb_t) (nLen:BN.meta_len) =
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
	(S.bn_mod_exp_f (as_seq h0 n) nInv (v bBits) (v bLen) (as_seq h0 b))
      (as_seq h0 aM, as_seq h0 accM))

inline_for_extraction noextract
val bn_mod_exp_loop:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_exp_loop_st t nLen

let bn_mod_exp_loop #t nLen #_ n nInv bBits bLen b aM accM =
  [@inline_let]
  let spec h0 = S.bn_mod_exp_f (as_seq h0 n) nInv (v bBits) (v bLen) (as_seq h0 b) in
  let h0 = ST.get () in
  loop2 h0 bBits aM accM spec
  (fun i ->
    Loops.unfold_repeati (v bBits) (spec h0) (as_seq h0 aM, as_seq h0 accM) (v i);
    let get_bit = BN.bn_get_ith_bit bLen b i in

    if not (Hacl.Bignum.Base.unsafe_bool_of_limb0 get_bit) then
      BM.mul n nInv aM accM accM; // acc = (acc * a) % n
    BM.sqr n nInv aM aM // a = (a * a) % n
  )


inline_for_extraction noextract
val bn_mod_exp_mont:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_exp_loop:bn_mod_exp_loop_st t nLen
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> acc:lbignum t nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> r2:lbignum t nLen
  -> res:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h acc /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint res acc /\
    disjoint a n /\ disjoint acc n /\ disjoint res r2 /\ disjoint r2 a /\
    disjoint r2 acc /\ disjoint r2 n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res ==
      S.bn_mod_exp_mont (v nLen) (as_seq h0 n) (as_seq h0 a) (as_seq h0 acc) (v bBits) (as_seq h0 b) (as_seq h0 r2))

let bn_mod_exp_mont #t nLen #_ bn_mod_exp_loop n a acc bBits b r2 res =
  push_frame ();
  let bLen = blocks bBits (size (bits t)) in
  let nInv = BM.mod_inv_limb n.(0ul) in // n * nInv = 1 (mod (pow2 64))

  let aM   = create nLen (uint #t 0) in
  let accM = create nLen (uint #t 0) in
  BM.to n nInv r2 a aM;
  BM.to n nInv r2 acc accM;
  bn_mod_exp_loop n nInv bBits bLen b aM accM;
  BM.from n nInv accM res;
  pop_frame ()


inline_for_extraction noextract
val mk_bn_mod_exp_precompr2:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_exp_loop:bn_mod_exp_loop_st t nLen ->
  bn_mod_exp_precompr2_st t nLen

let mk_bn_mod_exp_precompr2 #t nLen #_ bn_mod_exp_loop n a bBits b r2 res =
  push_frame ();
  let acc  = create nLen (uint #t 0) in
  BN.bn_from_uint nLen (uint #t 1) acc;
  bn_mod_exp_mont nLen bn_mod_exp_loop n a acc bBits b r2 res;
  pop_frame ()

/// A fully runtime implementation of modular exponentiation.

let bn_mod_exp_loop_runtime t nLen = bn_mod_exp_loop nLen #(BM.mk_runtime_mont t nLen)

[@CInline]
let bn_mod_exp_precompr2 #t nLen =
  mk_bn_mod_exp_precompr2 nLen #(BM.mk_runtime_mont t nLen) (bn_mod_exp_loop_runtime t nLen)


///
///  Montgomery ladder for exponentiation
///

inline_for_extraction noextract
let bn_mod_exp_mont_ladder_loop_st (t:limb_t) (nLen:BN.meta_len) =
    n:lbignum t nLen
  -> nInv:limb t
  -> bBits:size_t{v bBits > 0}
  -> bLen:size_t{v bLen = v (blocks bBits (size (bits t))) /\ (v bBits - 1) / bits t < v bLen}
  -> b:lbignum t bLen
  -> rM0:lbignum t nLen
  -> rM1:lbignum t nLen
  -> sw:lbignum t 1ul ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h rM0 /\ live h rM1 /\ live h sw /\
    disjoint rM0 rM1 /\ disjoint rM0 b /\ disjoint rM0 n /\
    disjoint rM1 b /\ disjoint rM1 n /\
    disjoint sw rM0 /\ disjoint sw rM1 /\ disjoint sw b /\ disjoint sw n)
  (ensures  fun h0 _ h1 -> modifies (loc rM0 |+| loc rM1 |+| loc sw) h0 h1 /\
    (as_seq h1 rM0, as_seq h1 rM1, LSeq.index (as_seq h1 sw) 0) ==
      Loops.repeat_gen (v bBits) (S.bn_mod_exp_mont_ladder_t t (v nLen) (v bBits))
	(S.bn_mod_exp_mont_ladder_f (as_seq h0 n) nInv (v bBits) (v bLen) (as_seq h0 b))
      (as_seq h0 rM0, as_seq h0 rM1, LSeq.index (as_seq h0 sw) 0))

inline_for_extraction noextract
val bn_mod_exp_mont_ladder_loop:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_exp_mont_ladder_loop_st t nLen

let bn_mod_exp_mont_ladder_loop #t nLen #_ n nInv bBits bLen b rM0 rM1 sw =
  [@inline_let]
  let refl h i : GTot (S.bn_mod_exp_mont_ladder_t t (v nLen) (v bBits) i) =
    (as_seq h rM0, as_seq h rM1, LSeq.index (as_seq h sw) 0) in
  [@inline_let]
  let footprint i = loc rM0 |+| loc rM1 |+| loc sw in
  [@inline_let]
  let spec h0 = S.bn_mod_exp_mont_ladder_f (as_seq h0 n) nInv (v bBits) (v bLen) (as_seq h0 b) in
  let h0 = ST.get () in
  loop h0 bBits (S.bn_mod_exp_mont_ladder_t t (v nLen) (v bBits)) refl footprint spec
  (fun i ->
    Loops.unfold_repeat_gen (v bBits)
      (S.bn_mod_exp_mont_ladder_t t (v nLen) (v bBits)) (spec h0) (refl h0 0) (v i);
    let bit = BN.bn_get_ith_bit bLen b (bBits -! i -! 1ul) in
    let sw1 = bit ^. sw.(0ul) in
    BN.cswap2 nLen sw1 rM0 rM1;
    BM.mul n nInv rM1 rM0 rM1;
    BM.sqr n nInv rM0 rM0;
    sw.(0ul) <- bit
  );
  let h1 = ST.get () in
  assert (refl h1 (v bBits) == Loops.repeat_gen (v bBits)
    (S.bn_mod_exp_mont_ladder_t t (v nLen) (v bBits)) (spec h0) (refl h0 0))


inline_for_extraction noextract
val bn_mod_exp_mont_ladder_:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_exp_mont_ladder_loop:bn_mod_exp_mont_ladder_loop_st t nLen
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> acc:lbignum t nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> r2:lbignum t nLen
  -> res:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h acc /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint res acc /\
    disjoint a n /\ disjoint acc n /\ disjoint r2 a /\ disjoint r2 res /\
    disjoint r2 acc /\ disjoint r2 n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res ==
      S.bn_mod_exp_mont_ladder_ (v nLen) (as_seq h0 n) (as_seq h0 a)
	(as_seq h0 acc) (v bBits) (as_seq h0 b) (as_seq h0 r2))

let bn_mod_exp_mont_ladder_ #t nLen #_ bn_mod_exp_mont_ladder_loop n a one bBits b r2 res =
  push_frame ();
  let bLen = blocks bBits (size (bits t)) in
  let nInv = BM.mod_inv_limb n.(0ul) in // n * nInv = 1 (mod (pow2 64))

  let rM0 = create nLen (uint #t 0) in
  let rM1 = create nLen (uint #t 0) in
  let sw  = create 1ul (uint #t 0) in
  BM.to n nInv r2 one rM0;
  BM.to n nInv r2 a rM1;

  bn_mod_exp_mont_ladder_loop n nInv bBits bLen b rM0 rM1 sw;
  BN.cswap2 nLen sw.(0ul) rM0 rM1;
  BM.from n nInv rM0 res;
  pop_frame ()


inline_for_extraction noextract
val mk_bn_mod_exp_mont_ladder_precompr2:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_exp_mont_ladder_loop:bn_mod_exp_mont_ladder_loop_st t nLen ->
  bn_mod_exp_mont_ladder_precompr2_st t nLen

let mk_bn_mod_exp_mont_ladder_precompr2 #t nLen #_ bn_mod_exp_mont_ladder_loop n a bBits b r2 res =
  push_frame ();
  let one  = create nLen (uint #t 0) in
  BN.bn_from_uint nLen (uint #t 1) one;
  bn_mod_exp_mont_ladder_ nLen bn_mod_exp_mont_ladder_loop n a one bBits b r2 res;
  pop_frame ()

/// A fully runtime implementation of modular exponentiation.

let bn_mod_exp_mont_ladder_loop_runtime t nLen = bn_mod_exp_mont_ladder_loop nLen #(BM.mk_runtime_mont t nLen)

[@CInline]
let bn_mod_exp_mont_ladder_precompr2 #t nLen =
  mk_bn_mod_exp_mont_ladder_precompr2 nLen #(BM.mk_runtime_mont t nLen) (bn_mod_exp_mont_ladder_loop_runtime t nLen)


inline_for_extraction noextract
val mk_bn_mod_exp:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_exp_loop:bn_mod_exp_loop_st t nLen ->
  bn_mod_exp_st t nLen

let mk_bn_mod_exp #t nLen #k bn_mod_exp_loop n a bBits b res =
  let h0 = ST.get () in
  let is_valid_m = mk_check_mod_exp nLen #k n a bBits b in
  push_frame ();
  let r2 = create nLen (uint #t 0) in
  BM.precomp n r2;
  mk_bn_mod_exp_precompr2 nLen #k bn_mod_exp_loop n a bBits b r2 res;
  let h1 = ST.get () in
  mapT nLen res (logand is_valid_m) res;
  let h2 = ST.get () in
  BD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    S.bn_mod_exp_lemma (v nLen) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b);
    assert (S.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h2 res)) end;
  pop_frame ();
  BB.unsafe_bool_of_limb is_valid_m


/// A fully runtime implementation of modular exponentiation.

[@CInline]
let bn_mod_exp #t nLen =
  mk_bn_mod_exp nLen #(BM.mk_runtime_mont t nLen) (bn_mod_exp_loop_runtime t nLen)


inline_for_extraction noextract
val mk_bn_mod_exp_mont_ladder:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_exp_mont_ladder_loop:bn_mod_exp_mont_ladder_loop_st t nLen ->
  bn_mod_exp_st t nLen

let mk_bn_mod_exp_mont_ladder #t nLen #k bn_mod_exp_mont_ladder_loop n a bBits b res =
  let h0 = ST.get () in
  let is_valid_m = mk_check_mod_exp nLen #k n a bBits b in
  push_frame ();
  let r2 = create nLen (uint #t 0) in
  BM.precomp n r2;
  mk_bn_mod_exp_mont_ladder_precompr2 nLen #k bn_mod_exp_mont_ladder_loop n a bBits b r2 res;
  let h1 = ST.get () in
  mapT nLen res (logand is_valid_m) res;
  let h2 = ST.get () in
  BD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    S.bn_mod_exp_mont_ladder_lemma (v nLen) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b);
    assert (S.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res)) end;
  pop_frame ();
  BB.unsafe_bool_of_limb is_valid_m


/// A fully runtime implementation of modular exponentiation.

[@CInline]
let bn_mod_exp_mont_ladder #t nLen =
  mk_bn_mod_exp_mont_ladder nLen #(BM.mk_runtime_mont t nLen) (bn_mod_exp_mont_ladder_loop_runtime t nLen)
