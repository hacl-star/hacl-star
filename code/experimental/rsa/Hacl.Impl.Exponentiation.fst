module Hacl.Impl.Exponentiation

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib
open Hacl.Impl.Montgomery
open Hacl.Impl.Multiplication
open Hacl.Impl.Shift

module Buffer = Spec.Lib.IntBuf

val mul_mod_mont:
  nLen:size_t ->
  rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t} ->
  pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i} ->
  n:lbignum nLen -> nInv_u64:uint64 -> st_kara:lbignum (add #SIZE (add #SIZE nLen nLen) (mul #SIZE (size 4) pow2_i)) ->
  aM:lbignum nLen -> bM:lbignum nLen -> resM:lbignum nLen ->
  Stack unit
    (requires (fun h -> live h aM /\ live h bM /\ live h resM /\ live h n /\ live h st_kara /\
                      disjoint st_kara aM /\ disjoint st_kara bM /\ disjoint st_kara n /\ disjoint resM st_kara))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 resM st_kara h0 h1))
  [@"c_inline"]
let mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM bM resM =
  let cLen = add #SIZE nLen nLen in
  let stLen = add #SIZE cLen (mul #SIZE (size 4) pow2_i) in
  let c = Buffer.sub st_kara (size 0) cLen in
  let tmp = Buffer.sub st_kara cLen (add #SIZE nLen rLen) in
  let h0 = FStar.HyperStack.ST.get() in
  karatsuba pow2_i nLen aM bM st_kara; // c = aM * bM
  let h1 = FStar.HyperStack.ST.get() in
  assert (modifies1 st_kara h0 h1);
  mont_reduction nLen rLen n nInv_u64 c tmp resM; // resM = c % n
  let h2 = FStar.HyperStack.ST.get() in
  assert (modifies2 resM tmp h1 h2)

val mod_exp_:
  nLen:size_t ->
  rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t} ->
  pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i} ->
  n:lbignum nLen -> nInv_u64:uint64 -> st_kara:lbignum (add #SIZE (add #SIZE nLen nLen) (mul #SIZE (size 4) pow2_i)) -> st_exp:lbignum (add #SIZE nLen nLen) ->
  bBits:size_t{0 < v bBits} -> bLen:size_t{v bLen = v (blocks bBits (size 64)) /\ (v bBits - 1) / 64 < v bLen} -> b:lbignum bLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h b /\ live h st_kara /\ live h st_exp /\
                      disjoint st_exp st_kara /\ disjoint st_kara n /\ disjoint st_kara st_exp))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 st_exp st_kara h0 h1))
  [@"c_inline"]
let mod_exp_ nLen rLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b =
  let aM = Buffer.sub st_exp (size 0) nLen in
  let accM = Buffer.sub st_exp nLen nLen in

  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 bBits st_exp st_kara
  (fun i ->
     let h0 = FStar.HyperStack.ST.get() in
     (if (bn_is_bit_set bLen b i) then begin
        mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM accM accM;
	let h1 = FStar.HyperStack.ST.get() in
	assert (modifies2 accM st_kara h0 h1) end
     else begin
       	let h1 = FStar.HyperStack.ST.get() in
	lemma_modifies0_is_modifies2 st_exp st_kara h0 h1 end); // acc = (acc * a) % n
      let h2 = FStar.HyperStack.ST.get() in
      mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM aM aM; // a = (a * a) % n
      let h3 = FStar.HyperStack.ST.get() in
      assert (modifies2 aM st_kara h2 h3)
  )

// res = a ^^ b mod n
val mod_exp:
  pow2_i:size_t -> modBits:size_t{0 < v modBits} ->
  nLen:size_t{128 * (v nLen + 1) < max_size_t /\ v nLen = v (blocks modBits (size 64)) /\ 6 * v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v nLen + 1 < 2 * v pow2_i} ->
  n:lbignum nLen -> a:lbignum nLen ->
  bBits:size_t{0 < v bBits} -> b:lbignum (blocks bBits (size 64)) -> res:lbignum nLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  #reset-options "--z3rlimit 150 --max_fuel 0"
  [@"c_inline"]
let mod_exp pow2_i modBits nLen n a bBits b res =
  let rLen = nLen +! size 1 in
  let exp_r = mul #SIZE (size 64) rLen in
  let exp2 = add #SIZE exp_r exp_r in

  let bLen = blocks bBits (size 64) in

  let karaLen = add #SIZE (add #SIZE nLen nLen) (mul #SIZE (size 4) pow2_i) in
  let stLen = add #SIZE (mul #SIZE (size 4) nLen) karaLen in

  let h0 = FStar.HyperStack.ST.get () in
  alloc1 #h0 stLen (u64 0) res
  (fun h -> (fun _ r -> True))
  (fun st ->
    let r2   = Buffer.sub st (size 0) nLen in
    let acc  = Buffer.sub st nLen nLen in
    let aM   = Buffer.sub st (mul #SIZE (size 2) nLen) nLen in
    let accM = Buffer.sub st (mul #SIZE (size 3) nLen) nLen in

    let st_exp  = Buffer.sub st (mul #SIZE (size 2) nLen) (mul #SIZE (size 2) nLen) in
    let st_kara = Buffer.sub st (mul #SIZE (size 4) nLen) karaLen in
    let tmp     = Buffer.sub #uint64 #(v stLen) #_ st (mul #SIZE (size 4) nLen) (add #SIZE nLen rLen) in

    acc.(size 0) <- u64 1;
    bn_pow2_mod_n nLen modBits n exp2 r2; // r2 = r * r % n
    let n0 = n.(size 0) in
    let nInv_u64 = mod_inv_u64 n0 in // n * nInv = 1 (mod (pow2 64))
    to_mont nLen rLen pow2_i n nInv_u64 r2 a st_kara aM;
    to_mont nLen rLen pow2_i n nInv_u64 r2 acc st_kara accM;
    mod_exp_ nLen rLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b;
    from_mont nLen rLen pow2_i n nInv_u64 accM tmp res; admit()
    )
