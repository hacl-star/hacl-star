module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum
open Hacl.Bignum.Montgomery

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Bignum.Exponentiation

friend Hacl.Spec.Bignum.Exponentiation


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_mod_exp_:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> bBits:size_t{v bBits > 0}
  -> bLen:size_t{v bLen = v (blocks bBits 64ul) /\ (v bBits - 1) / 64 < v bLen}
  -> b:lbignum bLen
  -> aM:lbignum rLen
  -> accM:lbignum rLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h b /\ live h aM /\ live h accM /\
    disjoint aM accM /\ disjoint aM b /\ disjoint aM n /\
    disjoint accM b /\ disjoint accM n)
  (ensures  fun h0 _ h1 -> modifies (loc aM |+| loc accM) h0 h1 /\
    (as_seq h1 aM, as_seq h1 accM) ==
      Lib.LoopCombinators.repeati (v bBits)
	(S.bn_mod_exp_f (as_seq h0 n) nInv_u64 (v bBits) (v bLen) (as_seq h0 b))
      (as_seq h0 aM, as_seq h0 accM))

[@CInline]
let bn_mod_exp_ nLen rLen n nInv_u64 bBits bLen b aM accM =
  [@inline_let]
  let spec h0 = S.bn_mod_exp_f (as_seq h0 n) nInv_u64 (v bBits) (v bLen) (as_seq h0 b) in
  let h0 = ST.get () in
  loop2 h0 bBits aM accM spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v bBits) (spec h0) (as_seq h0 aM, as_seq h0 accM) (v i);
    (if (bn_is_bit_set bLen b i) then
      mont_mul nLen rLen n nInv_u64 aM accM accM); // acc = (acc * a) % n
    mont_mul nLen rLen n nInv_u64 aM aM aM // a = (a * a) % n
  )


#set-options "--z3rlimit 100"

[@CInline]
let bn_mod_exp modBits nLen n r2 a bBits b res =
  push_frame ();
  let rLen = nLen +! 1ul in
  let bLen = blocks bBits 64ul in

  let acc  = create nLen (u64 0) in
  acc.(0ul) <- u64 1;
  let n0 = n.(0ul) in
  let nInv_u64 = mod_inv_u64 n0 in // n * nInv = 1 (mod (pow2 64))

  let aM   = create rLen (u64 0) in
  let accM = create rLen (u64 0) in
  to_mont nLen rLen n nInv_u64 r2 a aM;
  to_mont nLen rLen n nInv_u64 r2 acc accM;
  bn_mod_exp_ nLen rLen n nInv_u64 bBits bLen b aM accM;
  from_mont nLen rLen n nInv_u64 accM res;
  bn_sub_mask nLen n res;
  pop_frame ()
