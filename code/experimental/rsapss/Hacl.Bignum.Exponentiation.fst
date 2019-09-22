module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum
open Hacl.Bignum.Lib
open Hacl.Bignum.Montgomery
open Hacl.Bignum.Multiplication

module ST = FStar.HyperStack.ST


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val mul_mod_mont:
    nLen:size_t{v nLen > 0}
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum nLen
  -> bM:lbignum nLen
  -> resM:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h bM /\ live h resM /\ live h n /\
    eq_or_disjoint aM bM /\ 0 < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    bn_v h1 resM % bn_v h0 n == bn_v h0 aM * bn_v h0 bM / pow2 (64 * v rLen) % bn_v h0 n)

[@"c_inline"]
let mul_mod_mont nLen rLen n nInv_u64 aM bM resM =
  push_frame ();
  let cLen = nLen +! nLen in
  let c = create cLen (u64 0) in
  let tmpLen = nLen +! rLen in
  let tmp = create tmpLen (u64 0) in
  bn_mul nLen aM nLen bM c; // c = aM * bM
  mont_reduction nLen rLen n nInv_u64 c tmp resM; // resM = c % n
  admit();
  pop_frame ()


val mod_exp_:
    nLen:size_t{v nLen > 0}
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen <= max_size_t}
  -> n:lbignum nLen
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
    disjoint accM b /\ disjoint accM n /\
    0 < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc aM |+| loc accM) h0 h1)

[@"c_inline"]
let mod_exp_ nLen rLen n nInv_u64 bBits bLen b aM accM =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc aM |+| loc accM) h0 h1 in
  Lib.Loops.for 0ul bBits inv
  (fun i ->
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
    disjoint a r2 /\
    0 < bn_v h n /\ bn_v h r2 == pow2 (2 * 64 * (v nLen + 1)) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
// bn_v h1 res == fexp (bn_v h0 a) (bn_v h0 b) (bn_v h0 n)

[@"c_inline"]
let mod_exp modBits nLen n r2 a bBits b res =
  push_frame ();
  let rLen = nLen +! 1ul in
  let bLen = blocks bBits 64ul in

  let acc  = create nLen (u64 0) in
  let aM   = create nLen (u64 0) in
  let accM = create nLen (u64 0) in

  acc.(0ul) <- u64 1;
  let n0 = n.(0ul) in
  let nInv_u64 = mod_inv_u64 n0 in // n * nInv = 1 (mod (pow2 64))

  to_mont nLen rLen n nInv_u64 r2 a aM;
  to_mont nLen rLen n nInv_u64 r2 acc accM;
  mod_exp_ nLen rLen n nInv_u64 bBits bLen b aM accM;
  from_mont nLen rLen n nInv_u64 accM res;
  pop_frame ()
