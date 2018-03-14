module Hacl.Impl.Montgomery

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib
open Hacl.Impl.Addition
open Hacl.Impl.Comparison
open Hacl.Impl.Multiplication
open Hacl.Impl.Shift

module Buffer = Spec.Lib.IntBuf

val bn_pow2_mod_n_:
  #rLen:size_nat -> rrLen:size_t{v rrLen == rLen} ->
  a:lbignum rLen -> i:size_t -> p:size_t ->
  res:lbignum rLen -> 
  Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let rec bn_pow2_mod_n_ #rLen rrLen a i p res =
  if (i <. p) then begin
    bn_lshift1 #rLen rrLen res res;
    (if not (bn_is_less rrLen res rrLen a) then
      bn_sub rrLen res rrLen a res);
    bn_pow2_mod_n_ rrLen a (size_incr i) p res
  end

// res = 2 ^^ p % a
val bn_pow2_mod_n:
  #rLen:size_nat ->
  aBits:size_t ->
  rrLen:size_t{v rrLen == rLen /\ v aBits / 64 < rLen} -> a:lbignum rLen ->
  p:size_t{v aBits < v p} ->
  res:lbignum rLen ->
  Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let bn_pow2_mod_n #rLen aBits rrLen a p res =
  bn_set_bit rrLen res aBits;
  bn_sub rrLen res rrLen a res; // res = res - a
  bn_pow2_mod_n_ rrLen a aBits p res

val mod_inv_u64_:
  alpha:uint64 -> beta:uint64 -> ub:uint64 -> vb:uint64 -> i:size_t{v i <= 64} -> Tot uint64
  (decreases (64 - v i))
let rec mod_inv_u64_ alpha beta ub vb i =
  if (i <. size 64) then begin
    let u_is_odd = u64 0 -. (ub &. u64 1) in
    let beta_if_u_is_odd = beta &. u_is_odd in
    let ub = add_mod #U64 (shift_right #U64 (ub ^. beta_if_u_is_odd) (u32 1)) (ub &. beta_if_u_is_odd) in

    let alpha_if_u_is_odd = alpha &. u_is_odd in
    let vb = add_mod #U64 (shift_right #U64 vb (u32 1)) alpha_if_u_is_odd in
    mod_inv_u64_ alpha beta ub vb (size_incr i) end 
  else vb

val mod_inv_u64: n0:uint64 -> Tot uint64
let mod_inv_u64 n0 =
  let alpha = shift_left #U64 (u64 1) (u32 63) in
  let beta = n0 in

  let ub = u64 1 in
  let vb = u64 0 in
  mod_inv_u64_ alpha beta ub vb (size 0)

val mont_reduction_:
  #rLen:size_nat -> rrLen:size_t{v rrLen == rLen /\ rLen + rLen < max_size_t} ->
  c:lbignum (rLen + rLen) -> n:lbignum rLen -> nInv_u64:uint64 -> i:size_t -> 
  Stack unit
    (requires (fun h -> live h c /\ live h n /\ disjoint c n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 c h0 h1))
  [@"c_inline"]
let rec mont_reduction_ #rLen rrLen c n nInv_u64 i =
  if (i <. rrLen) then begin
    let ci = c.(i) in
    let qi = mul_mod #U64 nInv_u64 ci in
    bn_mult_by_limb_addj rrLen n qi (size 0) i (add #SIZE rrLen rrLen) (u64 0) c;
    mont_reduction_ rrLen c n nInv_u64 (size_incr i)
  end

val mont_reduction:
  #rLen:size_nat -> rrLen:size_t{v rrLen == rLen /\ rLen + rLen < max_size_t} ->
  n:lbignum rLen -> nInv_u64:uint64 ->
  c:lbignum (rLen + rLen) -> tmp:lbignum (rLen + rLen) -> res:lbignum rLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h c /\ live h tmp /\ live h res /\ disjoint tmp n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 res tmp h0 h1))
  [@"c_inline"]
let mont_reduction #rLen rrLen n nInv_u64 c tmp res =
  let rLen2 = add #SIZE rrLen rrLen in
  copy rLen2 c tmp;
  mont_reduction_ rrLen tmp n nInv_u64 (size 0);
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp' = Buffer.sub #uint64 #(v rLen2) #rLen tmp rrLen rrLen in
  copy rrLen tmp' res

val to_mont:
  #rLen:size_nat -> rrLen:size_t{v rrLen == rLen /\ rLen + rLen < max_size_t} ->
  pow2_i:size_t{2 * rLen + 4 * v pow2_i < max_size_t /\ rLen < v pow2_i} -> 
  iLen:size_t{v iLen < v pow2_i / 2 /\ v iLen + rLen = v pow2_i} ->
  n:lbignum rLen -> nInv_u64:uint64 ->
  r2:lbignum rLen -> a:lbignum rLen -> 
  st_kara:lbignum (2 * rLen + 4 * v pow2_i) -> aM:lbignum rLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h r2 /\ live h a /\ live h aM /\ live h st_kara))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1))
  [@"c_inline"]
let to_mont #rLen rrLen pow2_i iLen n nInv_u64 r2 a st_kara aM =
  let cLen = add #SIZE rrLen rrLen in
  let stLen = add #SIZE cLen (mul #SIZE (size 4) pow2_i) in
  
  let c = Buffer.sub #uint64 #(v stLen) #(v cLen) st_kara (size 0) cLen in
  let st_kara' = Buffer.sub #uint64 #(v stLen) #(4 * v pow2_i) st_kara cLen (mul #SIZE (size 4) pow2_i) in
  assume (disjoint c a /\ disjoint c r2 /\ disjoint st_kara' a /\ disjoint st_kara' r2);
  karatsuba #rLen pow2_i iLen rrLen a r2 st_kara' c; // c = a * r2
  assume (disjoint c n);
  mont_reduction #rLen rrLen n nInv_u64 c c aM // aM = c % n

val from_mont:
  #rLen:size_nat -> rrLen:size_t{v rrLen == rLen /\ rLen + rLen < max_size_t} ->
  pow2_i:size_t{2 * rLen + 4 * v pow2_i < max_size_t /\ rLen < v pow2_i} -> 
  iLen:size_t{v iLen < v pow2_i / 2 /\ v iLen + rLen = v pow2_i} ->
  n:lbignum rLen -> nInv_u64:uint64 ->
  aM:lbignum rLen -> st:lbignum (rLen + rLen) -> a:lbignum rLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h aM /\ live h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1))
  [@"c_inline"]
let from_mont #rLen rrLen pow2_i iLen n nInv_u64 aM st a =
  let rLen2 = add #SIZE rrLen rrLen in
  fill rLen2 st (u64 0);
  let st' = Buffer.sub #uint64 #(v rLen2) #rLen st (size 0) rrLen in
  copy rrLen aM st';
  assume (disjoint st n);
  mont_reduction #rLen rrLen n nInv_u64 st st a // a = aM % n

