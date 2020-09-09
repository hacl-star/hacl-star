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

friend Hacl.Spec.Bignum.Exponentiation


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mod_exp_loop_st (nLen: BN.meta_len) =
    n:lbignum nLen
  -> nInv_u64:uint64
  -> bBits:size_t{v bBits > 0}
  -> bLen:size_t{v bLen = v (blocks bBits 64ul) /\ (v bBits - 1) / 64 < v bLen}
  -> b:lbignum bLen
  -> aM:lbignum nLen
  -> accM:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h aM /\ live h accM /\
    disjoint aM accM /\ disjoint aM b /\ disjoint aM n /\
    disjoint accM b /\ disjoint accM n)
  (ensures  fun h0 _ h1 -> modifies (loc aM |+| loc accM) h0 h1 /\
    (as_seq h1 aM, as_seq h1 accM) ==
      Loops.repeati (v bBits)
	(S.bn_mod_exp_f (as_seq h0 n) nInv_u64 (v bBits) (v bLen) (as_seq h0 b))
      (as_seq h0 aM, as_seq h0 accM))

inline_for_extraction noextract
val bn_mod_exp_loop: nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_exp_loop_st nLen

let bn_mod_exp_loop nLen #_ n nInv_u64 bBits bLen b aM accM =
  [@inline_let]
  let spec h0 = S.bn_mod_exp_f (as_seq h0 n) nInv_u64 (v bBits) (v bLen) (as_seq h0 b) in
  let h0 = ST.get () in
  loop2 h0 bBits aM accM spec
  (fun i ->
    Loops.unfold_repeati (v bBits) (spec h0) (as_seq h0 aM, as_seq h0 accM) (v i);
    let get_bit = BN.bn_get_ith_bit bLen b i in

    if FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 get_bit =^ 1uL) then
      BM.mul n nInv_u64 aM accM accM; // acc = (acc * a) % n
    BM.sqr n nInv_u64 aM aM // a = (a * a) % n
  )


inline_for_extraction noextract
val bn_mod_exp_mont:
    nLen:size_t{0 < v nLen /\ 128 * v nLen <= max_size_t}
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_exp_loop:bn_mod_exp_loop_st nLen
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> acc:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> r2:lbignum nLen
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h acc /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint res acc /\
    disjoint a n /\ disjoint acc n /\ disjoint res r2 /\ disjoint r2 a /\
    disjoint r2 acc /\ disjoint r2 n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res ==
      S.bn_mod_exp_mont (v nLen) (as_seq h0 n) (as_seq h0 a) (as_seq h0 acc) (v bBits) (as_seq h0 b) (as_seq h0 r2))

let bn_mod_exp_mont nLen #_ bn_mod_exp_loop n a acc bBits b r2 res =
  push_frame ();
  let bLen = blocks bBits 64ul in
  let nInv_u64 = BM.mod_inv_u64 n.(0ul) in // n * nInv = 1 (mod (pow2 64))

  let aM   = create nLen (u64 0) in
  let accM = create nLen (u64 0) in
  BM.to n nInv_u64 r2 a aM;
  BM.to n nInv_u64 r2 acc accM;
  bn_mod_exp_loop n nInv_u64 bBits bLen b aM accM;
  BM.from n nInv_u64 accM res;
  pop_frame ()


inline_for_extraction noextract
val mk_bn_mod_exp_precompr2:
    nLen:size_t{0 < v nLen /\ 128 * v nLen <= max_size_t}
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_exp_loop:bn_mod_exp_loop_st nLen ->
  bn_mod_exp_precompr2_st nLen

let mk_bn_mod_exp_precompr2 nLen #_ bn_mod_exp_loop n a bBits b r2 res =
  push_frame ();
  let acc  = create nLen (u64 0) in
  BN.bn_from_uint nLen (u64 1) acc;
  bn_mod_exp_mont nLen bn_mod_exp_loop n a acc bBits b r2 res;
  pop_frame ()

/// A fully runtime implementation of modular exponentiation.

let bn_mod_exp_loop_runtime nLen = bn_mod_exp_loop nLen #(BM.mk_runtime_mont nLen)

[@CInline]
let bn_mod_exp_precompr2 nLen =
  mk_bn_mod_exp_precompr2 nLen #(BM.mk_runtime_mont nLen) (bn_mod_exp_loop_runtime nLen)


///
///  Montgomery ladder for exponentiation
///

inline_for_extraction noextract
let bn_mod_exp_mont_ladder_loop_st (nLen: BN.meta_len) =
    n:lbignum nLen
  -> nInv_u64:uint64
  -> bBits:size_t{v bBits > 0}
  -> bLen:size_t{v bLen = v (blocks bBits 64ul) /\ (v bBits - 1) / 64 < v bLen}
  -> b:lbignum bLen
  -> rM0:lbignum nLen
  -> rM1:lbignum nLen
  -> sw:lbignum 1ul ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h rM0 /\ live h rM1 /\ live h sw /\
    disjoint rM0 rM1 /\ disjoint rM0 b /\ disjoint rM0 n /\
    disjoint rM1 b /\ disjoint rM1 n /\
    disjoint sw rM0 /\ disjoint sw rM1 /\ disjoint sw b /\ disjoint sw n)
  (ensures  fun h0 _ h1 -> modifies (loc rM0 |+| loc rM1 |+| loc sw) h0 h1 /\
    (as_seq h1 rM0, as_seq h1 rM1, LSeq.index (as_seq h1 sw) 0) ==
      Loops.repeat_gen (v bBits) (S.bn_mod_exp_mont_ladder_t (v nLen) (v bBits))
	(S.bn_mod_exp_mont_ladder_f (as_seq h0 n) nInv_u64 (v bBits) (v bLen) (as_seq h0 b))
      (as_seq h0 rM0, as_seq h0 rM1, LSeq.index (as_seq h0 sw) 0))

inline_for_extraction noextract
val bn_mod_exp_mont_ladder_loop: nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_exp_mont_ladder_loop_st nLen

let bn_mod_exp_mont_ladder_loop nLen #_ n nInv_u64 bBits bLen b rM0 rM1 sw =
  [@inline_let]
  let refl h i : GTot (S.bn_mod_exp_mont_ladder_t (v nLen) (v bBits) i) =
    (as_seq h rM0, as_seq h rM1, LSeq.index (as_seq h sw) 0) in
  [@inline_let]
  let footprint i = loc rM0 |+| loc rM1 |+| loc sw in
  [@inline_let]
  let spec h0 = S.bn_mod_exp_mont_ladder_f #(v nLen) (as_seq h0 n) nInv_u64 (v bBits) (v bLen) (as_seq h0 b) in
  let h0 = ST.get () in
  loop h0 bBits (S.bn_mod_exp_mont_ladder_t (v nLen) (v bBits)) refl footprint spec
  (fun i ->
    Loops.unfold_repeat_gen (v bBits) (S.bn_mod_exp_mont_ladder_t (v nLen) (v bBits)) (spec h0) (refl h0 0) (v i);
    let bit = BN.bn_get_ith_bit bLen b (bBits -! i -! 1ul) in
    let sw1 = bit ^. sw.(0ul) in
    BN.cswap2 nLen sw1 rM0 rM1;
    BM.mul n nInv_u64 rM1 rM0 rM1;
    BM.sqr n nInv_u64 rM0 rM0;
    sw.(0ul) <- bit
  );
  let h1 = ST.get () in
  assert (refl h1 (v bBits) == Loops.repeat_gen (v bBits) (S.bn_mod_exp_mont_ladder_t (v nLen) (v bBits)) (spec h0) (refl h0 0))


inline_for_extraction noextract
val bn_mod_exp_mont_ladder_:
    nLen:size_t{0 < v nLen /\ 128 * v nLen <= max_size_t}
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_exp_mont_ladder_loop:bn_mod_exp_mont_ladder_loop_st nLen
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> acc:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> r2:lbignum nLen
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h acc /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint res acc /\
    disjoint a n /\ disjoint acc n /\ disjoint r2 a /\ disjoint r2 res /\
    disjoint r2 acc /\ disjoint r2 n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res ==
      S.bn_mod_exp_mont_ladder_ (v nLen) (as_seq h0 n) (as_seq h0 a) (as_seq h0 acc) (v bBits) (as_seq h0 b) (as_seq h0 r2))

let bn_mod_exp_mont_ladder_ nLen #_ bn_mod_exp_mont_ladder_loop n a one bBits b r2 res =
  push_frame ();
  let bLen = blocks bBits 64ul in
  let nInv_u64 = BM.mod_inv_u64 n.(0ul) in // n * nInv = 1 (mod (pow2 64))

  let rM0 = create nLen (u64 0) in
  let rM1 = create nLen (u64 0) in
  let sw  = create 1ul (u64 0) in
  BM.to n nInv_u64 r2 one rM0;
  BM.to n nInv_u64 r2 a rM1;

  bn_mod_exp_mont_ladder_loop n nInv_u64 bBits bLen b rM0 rM1 sw;
  BN.cswap2 nLen sw.(0ul) rM0 rM1;
  BM.from n nInv_u64 rM0 res;
  pop_frame ()


inline_for_extraction noextract
val mk_bn_mod_exp_mont_ladder_precompr2:
    nLen:size_t{0 < v nLen /\ 128 * v nLen <= max_size_t}
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_exp_mont_ladder_loop:bn_mod_exp_mont_ladder_loop_st nLen ->
  bn_mod_exp_mont_ladder_precompr2_st nLen

let mk_bn_mod_exp_mont_ladder_precompr2 nLen #_ bn_mod_exp_mont_ladder_loop n a bBits b r2 res =
  push_frame ();
  let one  = create nLen (u64 0) in
  BN.bn_from_uint nLen (u64 1) one;
  bn_mod_exp_mont_ladder_ nLen bn_mod_exp_mont_ladder_loop n a one bBits b r2 res;
  pop_frame ()

/// A fully runtime implementation of modular exponentiation.

let bn_mod_exp_mont_ladder_loop_runtime nLen = bn_mod_exp_mont_ladder_loop nLen #(BM.mk_runtime_mont nLen)

[@CInline]
let bn_mod_exp_mont_ladder_precompr2 nLen =
  mk_bn_mod_exp_mont_ladder_precompr2 nLen #(BM.mk_runtime_mont nLen) (bn_mod_exp_mont_ladder_loop_runtime nLen)


inline_for_extraction noextract
val mk_bn_mod_exp:
    nLen:size_t{0 < v nLen /\ 128 * v nLen <= max_size_t}
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_exp_loop:bn_mod_exp_loop_st nLen ->
  bn_mod_exp_st nLen

let mk_bn_mod_exp nLen #k bn_mod_exp_loop n a bBits b res =
  push_frame ();
  let r2 = create nLen (u64 0) in
  BM.precomp n r2;
  mk_bn_mod_exp_precompr2 nLen #k bn_mod_exp_loop n a bBits b r2 res;
  pop_frame ()


/// A fully runtime implementation of modular exponentiation.

[@CInline]
let bn_mod_exp nLen =
  mk_bn_mod_exp nLen #(BM.mk_runtime_mont nLen) (bn_mod_exp_loop_runtime nLen)


inline_for_extraction noextract
val mk_bn_mod_exp_mont_ladder:
    nLen:size_t{0 < v nLen /\ 128 * v nLen <= max_size_t}
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_exp_mont_ladder_loop:bn_mod_exp_mont_ladder_loop_st nLen ->
  bn_mod_exp_mont_ladder_st nLen

let mk_bn_mod_exp_mont_ladder nLen #k bn_mod_exp_mont_ladder_loop n a bBits b res =
  push_frame ();
  let r2 = create nLen (u64 0) in
  BM.precomp n r2;
  mk_bn_mod_exp_mont_ladder_precompr2 nLen #k bn_mod_exp_mont_ladder_loop n a bBits b r2 res;
  pop_frame ()


/// A fully runtime implementation of modular exponentiation.

[@CInline]
let bn_mod_exp_mont_ladder nLen =
  mk_bn_mod_exp_mont_ladder nLen #(BM.mk_runtime_mont nLen) (bn_mod_exp_mont_ladder_loop_runtime nLen)
