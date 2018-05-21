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
  alpha:uint64 -> beta:uint64 -> uv:lbignum (size 2) -> Stack unit
  (requires (fun h -> live h uv))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 uv h0 h1))
  [@ "substitute"]
let mod_inv_u64_ alpha beta uv =
  iteri_simple (size 64)
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
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))
  [@"c_inline"]
let mod_inv_u64 n0 =
  let alpha = shift_left #U64 (u64 1) (u32 63) in
  let beta = n0 in
  alloc (size 2) (u64 0) [] []
  (fun h0 _ h1 -> True)
  (fun uv ->
    uv.(size 0) <- u64 1;
    uv.(size 1) <- u64 0;
    mod_inv_u64_ alpha beta uv;
    uv.(size 1)
  )

val mont_reduction_f:
  nLen:size_t ->
  rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t} ->
  c:lbignum (add #SIZE nLen rLen) -> n:lbignum nLen -> nInv_u64:uint64 ->
  carry:lbignum (size 1) -> i:size_t{v i < v nLen} -> Stack unit
  (requires (fun h -> live h c /\ live h n /\ live h carry /\ disjoint c n))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry c h0 h1))
  [@ "substitute"]
let mont_reduction_f nLen rLen c n nInv_u64 carry i =
  let ci = c.(i) in
  let qi = mul_mod #U64 nInv_u64 ci in
  (* FIX: res = res + limb * bn * beta ^ i *)
  bn_mult_by_limb_addj nLen n qi i (add #SIZE nLen rLen) c carry;
  let c_ni =  c.(add #SIZE nLen i) in
  let (c1, c_ni) = addcarry_u64 (u64 0) c_ni carry.(size 0) in
  c.(add #SIZE nLen i) <- c_ni;
  let c_ni1 = c.(add #SIZE (add #SIZE nLen i) (size 1)) in
  c.(add #SIZE (add #SIZE nLen i) (size 1)) <- add_mod #U64 c_ni1 c1

val mont_reduction_:
  nLen:size_t ->
  rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t} ->
  c:lbignum (add #SIZE nLen rLen) -> n:lbignum nLen -> nInv_u64:uint64 ->
  carry:lbignum (size 1) -> Stack unit
  (requires (fun h -> live h c /\ live h n /\ live h carry /\ disjoint c n))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry c h0 h1))
  [@ "substitute"]
let mont_reduction_ nLen rLen c n nInv_u64 carry =
  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 nLen carry c
  (fun i ->
    carry.(size 0) <- u64 0;
    mont_reduction_f nLen rLen c n nInv_u64 carry i
  );
  let ci = c.(nLen) in
  let qi = mul_mod #U64 nInv_u64 ci in
  bn_mult_by_limb_addj nLen n qi nLen (add #SIZE nLen rLen) c carry;
  let c_ni =  c.(add #SIZE nLen nLen) in
  let c1 = carry.(size 0) in
  c.(add #SIZE nLen nLen) <- add_mod #U64 c_ni c1

val mont_reduction_a:
  nLen:size_t ->
  rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t} ->
  c:lbignum (add #SIZE nLen rLen) -> n:lbignum nLen -> nInv_u64:uint64 -> Stack unit
  (requires (fun h -> live h c /\ live h n /\  disjoint c n))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 c h0 h1))
  [@"c_inline"]
let mont_reduction_a nLen rLen c n nInv_u64 =
  let h0 = FStar.HyperStack.ST.get () in
  alloc1 #h0 (size 1) (u64 0) c
  (fun h -> (fun _ r -> True))
  (fun carry ->
    mont_reduction_ nLen rLen c n nInv_u64 carry
  )

val mont_reduction:
  nLen:size_t ->
  rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t} ->
  n:lbignum nLen -> nInv_u64:uint64 ->
  c:lbignum (add #SIZE nLen nLen) -> tmp:lbignum (add #SIZE nLen rLen) ->
  res:lbignum nLen -> Stack unit
  (requires (fun h -> live h n /\ live h c /\ live h tmp /\ live h res /\ disjoint tmp n))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 res tmp h0 h1))
  [@"c_inline"]
let mont_reduction nLen rLen n nInv_u64 c tmp res =
  let nLen2 = add #SIZE nLen nLen in
  let tmp1 = Buffer.sub tmp (size 0) nLen2 in
  copy tmp1 nLen2 c;
  tmp.(nLen2) <- u64 0;
  mont_reduction_a nLen rLen tmp n nInv_u64;
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp1 = Buffer.sub tmp rLen nLen in
  copy res nLen tmp1

val to_mont:
  nLen:size_t ->
  rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t} ->
  pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i} ->
  n:lbignum nLen -> nInv_u64:uint64 ->
  r2:lbignum nLen -> a:lbignum nLen ->
  st_kara:lbignum (add #SIZE (add #SIZE nLen nLen) (mul #SIZE (size 4) pow2_i)) -> aM:lbignum nLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h r2 /\ live h a /\ live h aM /\ live h st_kara /\
                      disjoint st_kara a /\ disjoint st_kara r2 /\ disjoint st_kara n /\
		      disjoint aM st_kara /\ disjoint st_kara aM))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 aM st_kara h0 h1))
  [@"c_inline"]
let to_mont nLen rLen pow2_i n nInv_u64 r2 a st_kara aM =
  let cLen = add #SIZE nLen nLen in
  let stLen = add #SIZE cLen (mul #SIZE (size 4) pow2_i) in
  let c = Buffer.sub #uint64 #(v stLen) #(v cLen) st_kara (size 0) cLen in
  let h0 = FStar.HyperStack.ST.get () in
  karatsuba pow2_i nLen a r2 st_kara; // c = a * r2
  let h1 = FStar.HyperStack.ST.get () in
  assert (modifies1 st_kara h0 h1);
  let tmp = Buffer.sub st_kara cLen (add #SIZE nLen rLen) in
  mont_reduction nLen rLen n nInv_u64 c tmp aM; // aM = c % n
  let h2 = FStar.HyperStack.ST.get () in
  assert (modifies2 aM tmp h1 h2)

val from_mont:
  nLen:size_t ->
  rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t} ->
  pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i} ->
  n:lbignum nLen -> nInv_u64:uint64 ->
  aM:lbignum nLen -> tmp:lbignum (add #SIZE nLen rLen) -> a:lbignum nLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h aM /\ live h tmp /\ disjoint tmp n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 a tmp h0 h1))
  [@"c_inline"]
let from_mont nLen rLen pow2_i n nInv_u64 aM tmp a =
  let tmpLen = add #SIZE nLen rLen in
  fill tmpLen tmp (u64 0);
  let tmp1 = Buffer.sub tmp (size 0) nLen in
  copy tmp1 nLen aM;
  mont_reduction_a nLen rLen tmp n nInv_u64;
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp1 = Buffer.sub tmp rLen nLen in
  copy a nLen tmp1
