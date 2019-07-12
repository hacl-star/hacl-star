module Hacl.Impl.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib
open Hacl.Impl.Montgomery
open Hacl.Impl.Multiplication

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val mul_mod_mont:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> st_kara:lbignum (nLen +. nLen +. 4ul *. pow2_i)
  -> aM:lbignum nLen
  -> bM:lbignum nLen
  -> resM:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h aM /\ live h bM /\ live h resM /\ live h n /\ live h st_kara /\
      disjoint st_kara aM /\ disjoint st_kara bM /\ disjoint st_kara n /\ disjoint resM st_kara)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer resM) (loc_buffer st_kara)) h0 h1)
[@"c_inline"]    
let mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM bM resM =
  let cLen = nLen +. nLen in
  let stLen = cLen +. 4ul *. pow2_i in
  let c = sub st_kara 0ul cLen in
  let tmp = sub st_kara cLen (nLen +. rLen) in
  karatsuba pow2_i nLen aM bM st_kara; // c = aM * bM
  mont_reduction nLen rLen n nInv_u64 c tmp resM // resM = c % n

val mod_exp_:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> st_kara:lbignum (nLen +. nLen +. 4ul *. pow2_i)
  -> st_exp:lbignum (nLen +. nLen)
  -> bBits:size_t{v bBits > 0}
  -> bLen:size_t{v bLen = v (blocks bBits 64ul) /\ (v bBits - 1) / 64 < v bLen}
  -> b:lbignum bLen
  -> Stack unit
    (requires fun h ->
      live h n /\ live h b /\ live h st_kara /\ live h st_exp /\
      disjoint st_exp st_kara /\ disjoint st_kara n /\ disjoint st_kara st_exp)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer st_exp) (loc_buffer st_kara)) h0 h1)
[@"c_inline"]
let mod_exp_ nLen rLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b =
  let aM = sub st_exp 0ul nLen in
  let accM = sub st_exp nLen nLen in

  let h0 = ST.get () in
  let inv h1 i = modifies (loc_union (loc_buffer st_exp) (loc_buffer st_kara)) h0 h1 in
  Lib.Loops.for 0ul bBits inv
  (fun i ->
    (if (bn_is_bit_set bLen b i) then
      mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM accM accM); // acc = (acc * a) % n
    mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM aM aM // a = (a * a) % n
  )

//128 * (v nLen + 1) < max_size_t
// res = a ^^ b mod n
val mod_exp:
    pow2_i:size_t
  -> modBits:size_t{v modBits > 0}
  -> nLen:size_t{0 < v nLen /\ v nLen = v (blocks modBits 64ul) /\
    5 * v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v nLen + 1 < 2 * v pow2_i}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h -> live h n /\ live h a /\ live h b /\ live h res /\ live h r2)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let mod_exp pow2_i modBits nLen n r2 a bBits b res = admit();
  push_frame ();
  let rLen = nLen +. 1ul in
  let exp_r = 64ul *. rLen in
  let exp2 = exp_r +. exp_r in

  let bLen = blocks bBits 64ul in

  let karaLen = nLen +! nLen +! 4ul *! pow2_i in
  let stLen = nLen +! nLen +! nLen +! karaLen in
  assume (0 < v stLen);
  let st = create stLen (u64 0) in

  let acc  = sub st 0ul nLen in
  let aM   = sub st nLen nLen in
  let accM = sub st (nLen +. nLen) nLen in

  let st_exp  = sub st nLen (nLen +. nLen) in
  let st_kara = sub st (nLen +. nLen +. nLen) karaLen in
  let tmp     = sub #_ #(v stLen) #(v nLen + v rLen) st (nLen +. nLen +. nLen) (nLen +. rLen) in

  acc.(0ul) <- u64 1;
  let n0 = n.(0ul) in
  let nInv_u64 = mod_inv_u64 n0 in // n * nInv = 1 (mod (pow2 64))
  to_mont nLen rLen pow2_i n nInv_u64 r2 a st_kara aM;
  to_mont nLen rLen pow2_i n nInv_u64 r2 acc st_kara accM;
  mod_exp_ nLen rLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b;
  from_mont nLen rLen pow2_i n nInv_u64 accM tmp res;
  pop_frame ()
