module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum
open Hacl.Bignum.Base
open Hacl.Bignum.Montgomery
open Hacl.Bignum.Montgomery.PreCompConstants

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Bignum.Exponentiation


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_is_bit_set:
    len:size_t
  -> input:lbignum len
  -> ind:size_t{v ind / 64 < v len} ->
  Stack bool
  (requires fun h -> live h input)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_is_bit_set (as_seq h0 input) (v ind))

[@CInline]
let bn_is_bit_set len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  let tmp = input.(i) in
  let tmp = (tmp >>. j) &. u64 1 in
  eq_u64 tmp (u64 1)


val mod_exp_:
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
    disjoint accM b /\ disjoint accM n /\
    0 < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc aM |+| loc accM) h0 h1 /\
    (as_seq h1 aM, as_seq h1 accM) ==
      Lib.LoopCombinators.repeati (v bBits)
	(S.mod_exp_f (as_seq h0 n) nInv_u64 (v bBits) (v bLen) (as_seq h0 b))
      (as_seq h0 aM, as_seq h0 accM))

[@CInline]
let mod_exp_ nLen rLen n nInv_u64 bBits bLen b aM accM =
  [@inline_let]
  let spec h0 = S.mod_exp_f (as_seq h0 n) nInv_u64 (v bBits) (v bLen) (as_seq h0 b) in
  let h0 = ST.get () in
  loop2 h0 bBits aM accM spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v bBits) (spec h0) (as_seq h0 aM, as_seq h0 accM) (v i);
    (if (bn_is_bit_set bLen b i) then
      mul_mod_mont nLen rLen n nInv_u64 aM accM accM); // acc = (acc * a) % n
    mul_mod_mont nLen rLen n nInv_u64 aM aM aM // a = (a * a) % n
  )


val mod_exp:
    modBits:size_t{v modBits > 0}
  -> nLen:size_t{0 < v nLen /\ v nLen = v (blocks modBits 64ul) /\ 128 * (v nLen + 1) <= max_size_t}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint res r2 /\
    disjoint a r2 /\ disjoint a n /\ disjoint n r2 /\
    0 < bn_v h n /\ bn_v h r2 == pow2 (2 * 64 * (v nLen + 1)) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.mod_exp (v modBits) (v nLen) (as_seq h0 n) (as_seq h0 r2) (as_seq h0 a) (v bBits) (as_seq h0 b))

[@CInline]
let mod_exp modBits nLen n r2 a bBits b res =
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
  mod_exp_ nLen rLen n nInv_u64 bBits bLen b aM accM;
  from_mont nLen rLen n nInv_u64 accM res;
  pop_frame ()
