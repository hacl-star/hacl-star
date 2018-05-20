module Hacl.Impl.Montgomery

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib
open Hacl.Impl.Addition
open Hacl.Impl.Multiplication

module Buffer = Spec.Lib.IntBuf

val mod_inv_u64_:
  alpha:uint64 -> beta:uint64 -> uv:lbignum 2 -> Stack unit
  (requires (fun h -> live h uv))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 uv h0 h1))
  [@ "substitute"]
let mod_inv_u64_ alpha beta uv =
  iteri_simple #uint64 #2 (size 64)
  (fun i uv ->
    let ub = uv.(size 0) in
    let vb = uv.(size 1) in
    let u_is_odd = u64 0 -. (ub &. u64 1) in
    let beta_if_u_is_odd = beta &. u_is_odd in
    uv.(size 0) <- add_mod #U64 (shift_right #U64 (ub ^. beta_if_u_is_odd) (u32 1)) (ub &. beta_if_u_is_odd);

    let alpha_if_u_is_odd = alpha &. u_is_odd in
    uv.(size 1) <- add_mod #U64 (shift_right #U64 vb (u32 1)) alpha_if_u_is_odd
  ) uv

val mod_inv_u64: n0:uint64 -> Stack uint64
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies0 h0 h1))
  [@"c_inline"]
let mod_inv_u64 n0 =
  let alpha = shift_left #U64 (u64 1) (u32 63) in
  let beta = n0 in
  alloc #uint64 #uint64 #2 (size 2) (u64 0) [] []
  (fun h0 _ h1 -> True)
  (fun uv ->
    uv.(size 0) <- u64 1;
    uv.(size 1) <- u64 0;
    mod_inv_u64_ alpha beta uv;
    uv.(size 1)
  )

val mont_reduction_f:
  #nLen:size_nat -> #rLen:size_nat{nLen < rLen} ->
  nnLen:size_t{v nnLen == nLen} ->
  rrLen:size_t{v rrLen == rLen /\ nLen + rLen < max_size_t} ->
  c:lbignum (nLen + rLen) -> n:lbignum nLen -> nInv_u64:uint64 ->
  carry:lbignum 1 -> i:size_t{v i < nLen} -> Stack unit
  (requires (fun h -> live h c /\ live h n /\ live h carry /\ disjoint c n))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry c h0 h1))
  [@ "substitute"]
let mont_reduction_f #nLen #rLen nnLen rrLen c n nInv_u64 carry i =
  let ci = c.(i) in
  let qi = mul_mod #U64 nInv_u64 ci in
  (* FIX: res = res + limb * bn * beta ^ i *)
  bn_mult_by_limb_addj nnLen n qi i (add #SIZE nnLen rrLen) c carry;
  let c_ni =  c.(add #SIZE nnLen i) in
  let (c1, c_ni) = addcarry_u64 (u64 0) c_ni carry.(size 0) in
  c.(add #SIZE nnLen i) <- c_ni;
  let c_ni1 = c.(add #SIZE (add #SIZE nnLen i) (size 1)) in
  c.(add #SIZE (add #SIZE nnLen i) (size 1)) <- add_mod #U64 c_ni1 c1

val mont_reduction_:
  #nLen:size_nat -> #rLen:size_nat{nLen < rLen} ->
  nnLen:size_t{v nnLen == nLen} ->
  rrLen:size_t{v rrLen == rLen /\ nLen + rLen < max_size_t} ->
  c:lbignum (nLen + rLen) -> n:lbignum nLen -> nInv_u64:uint64 ->
  carry:lbignum 1 -> Stack unit
  (requires (fun h -> live h c /\ live h n /\ live h carry /\ disjoint c n))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry c h0 h1))
  [@ "substitute"]
let mont_reduction_ #nLen #rLen nnLen rrLen c n nInv_u64 carry =
  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 #uint64 #uint64 #1 #(nLen + rLen) nnLen carry c
  (fun i ->
    carry.(size 0) <- u64 0;
    mont_reduction_f #nLen #rLen nnLen rrLen c n nInv_u64 carry i
  );
  let ci = c.(nnLen) in
  let qi = mul_mod #U64 nInv_u64 ci in
  bn_mult_by_limb_addj nnLen n qi nnLen (add #SIZE nnLen rrLen) c carry;
  let c_ni =  c.(add #SIZE nnLen nnLen) in
  let c1 = carry.(size 0) in
  c.(add #SIZE nnLen nnLen) <- add_mod #U64 c_ni c1

val mont_reduction_a:
  #nLen:size_nat -> #rLen:size_nat{nLen < rLen} ->
  nnLen:size_t{v nnLen == nLen} ->
  rrLen:size_t{v rrLen == rLen /\ nLen + rLen < max_size_t} ->
  c:lbignum (nLen + rLen) -> n:lbignum nLen -> nInv_u64:uint64 -> Stack unit
  (requires (fun h -> live h c /\ live h n /\  disjoint c n))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 c h0 h1))
  [@"c_inline"]
let mont_reduction_a #nLen #rLen nnLen rrLen c n nInv_u64 =
  alloc #uint64 #unit #1 (size 1) (u64 0) [BufItem n] [BufItem c]
  (fun h0 _ h1 -> True)
  (fun carry ->
    mont_reduction_ #nLen #rLen nnLen rrLen c n nInv_u64 carry
  )

val mont_reduction:
  #nLen:size_nat -> #rLen:size_nat{nLen < rLen} ->
  nnLen:size_t{v nnLen == nLen} ->
  rrLen:size_t{v rrLen == rLen /\ nLen + rLen < max_size_t} ->
  n:lbignum nLen -> nInv_u64:uint64 ->
  c:lbignum (nLen + nLen) -> tmp:lbignum (nLen + rLen) ->
  res:lbignum nLen -> Stack unit
  (requires (fun h -> live h n /\ live h c /\ live h tmp /\ live h res /\ disjoint tmp n))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 res tmp h0 h1))
  [@"c_inline"]
let mont_reduction #nLen #rLen nnLen rrLen n nInv_u64 c tmp res =
  let nLen2 = add #SIZE nnLen nnLen in
  let tmp1 = Buffer.sub #uint64 #(nLen +rLen) #(v nLen2) tmp (size 0) nLen2 in
  copy tmp1 nLen2 c;
  tmp.(nLen2) <- u64 0;
  mont_reduction_a nnLen rrLen tmp n nInv_u64;
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp1 = Buffer.sub #uint64 #(nLen + rLen) #nLen tmp rrLen nnLen in
  copy res nnLen tmp1

#reset-options "--lax"

val to_mont:
  #nLen:size_nat -> #rLen:size_nat{nLen < rLen} ->
  nnLen:size_t{v nnLen == nLen} ->
  rrLen:size_t{v rrLen == rLen /\ nLen + rLen < max_size_t} ->
  pow2_i:size_t{2 * nLen + 4 * v pow2_i < max_size_t /\ nLen <= v pow2_i /\ rLen < 2 * v pow2_i} ->
  n:lbignum nLen -> nInv_u64:uint64 ->
  r2:lbignum nLen -> a:lbignum nLen ->
  st_kara:lbignum (2 * nLen + 4 * v pow2_i) -> aM:lbignum nLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h r2 /\ live h a /\ live h aM /\ live h st_kara /\
                      disjoint st_kara a /\ disjoint st_kara r2 /\ disjoint st_kara n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 aM st_kara h0 h1))
  [@"c_inline"]
let to_mont #nLen #rLen nnLen rrLen pow2_i n nInv_u64 r2 a st_kara aM =
  let cLen = add #SIZE nnLen nnLen in
  let stLen = add #SIZE cLen (mul #SIZE (size 4) pow2_i) in
  let c = Buffer.sub #uint64 #(v stLen) #(v cLen) st_kara (size 0) cLen in
  karatsuba pow2_i nnLen a r2 st_kara; // c = a * r2
  let tmp = Buffer.sub #uint64 #(v stLen) #(nLen + rLen) st_kara cLen (add #SIZE nnLen rrLen) in
  mont_reduction #nLen #rLen nnLen rrLen n nInv_u64 c tmp aM // aM = c % n

#reset-options "--z3rlimit 30"

val from_mont:
  #nLen:size_nat -> #rLen:size_nat{nLen < rLen} ->
  nnLen:size_t{v nnLen == nLen} ->
  rrLen:size_t{v rrLen == rLen /\ nLen + rLen < max_size_t} ->
  pow2_i:size_t{2 * nLen + 4 * v pow2_i < max_size_t /\ nLen <= v pow2_i /\ rLen < 2 * v pow2_i} ->
  n:lbignum nLen -> nInv_u64:uint64 ->
  aM:lbignum nLen -> tmp:lbignum (nLen + rLen) -> a:lbignum nLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h aM /\ live h tmp /\ disjoint tmp n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 a tmp h0 h1))
  [@"c_inline"]
let from_mont #nLen #rLen nnLen rrLen pow2_i n nInv_u64 aM tmp a =
  let tmpLen = add #SIZE nnLen rrLen in
  fill tmpLen tmp (u64 0);
  let tmp1 = Buffer.sub #uint64 #(v tmpLen) #nLen tmp (size 0) nnLen in
  copy tmp1 nnLen aM;
  mont_reduction_a nnLen rrLen tmp n nInv_u64;
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp1 = Buffer.sub #uint64 #(v tmpLen) #nLen tmp rrLen nnLen in
  copy a nnLen tmp1
