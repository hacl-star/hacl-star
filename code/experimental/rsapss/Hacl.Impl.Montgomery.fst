module Hacl.Impl.Montgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib
open Hacl.Impl.Addition
open Hacl.Impl.Multiplication

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val mod_inv_u64_:
    alpha:uint64
  -> beta:uint64
  -> uv:lbignum 2ul
  -> Stack unit
    (requires fun h -> live h uv)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer uv) h0 h1)
let mod_inv_u64_ alpha beta uv =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_buffer uv) h0 h1 in
  Lib.Loops.for 0ul 64ul inv
  (fun i ->
    let ub = uv.(0ul) in
    let vb = uv.(1ul) in
    let u_is_odd = u64 0 -. (ub &. u64 1) in
    let beta_if_u_is_odd = beta &. u_is_odd in
    uv.(0ul) <- ((ub ^. beta_if_u_is_odd) >>. 1ul) +. (ub &. beta_if_u_is_odd);

    let alpha_if_u_is_odd = alpha &. u_is_odd in
    uv.(1ul) <- (vb >>. 1ul) +. alpha_if_u_is_odd
  )

val mod_inv_u64:
    n0:uint64
  -> Stack uint64
    (requires fun h -> True)
    (ensures  fun h0 _ h1 -> modifies loc_none h0 h1)
[@"c_inline"]
let mod_inv_u64 n0 =
  push_frame ();
  let alpha = u64 1 <<. 63ul in
  let beta = n0 in
  let uv = create 2ul (u64 0) in
  uv.(0ul) <- u64 1;
  uv.(1ul) <- u64 0;
  mod_inv_u64_ alpha beta uv;
  let res = uv.(1ul) in
  pop_frame ();
  res

inline_for_extraction noextract
val mont_reduction_f:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> c:lbignum (nLen +. rLen)
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> carry:lbignum 1ul
  -> i:size_t{v i < v rLen}
  -> Stack unit
    (requires fun h -> live h c /\ live h n /\ live h carry /\ disjoint c n)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer carry) (loc_buffer c)) h0 h1)
let mont_reduction_f nLen rLen c n nInv_u64 carry i =
  let ci = c.(i) in
  let qi = nInv_u64 *. ci in
  let _ = bn_mult_by_limb_addj_add nLen n qi i (nLen +. rLen) c carry in ()

inline_for_extraction noextract
val mont_reduction_:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> c:lbignum (nLen +. rLen)
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> carry:lbignum 1ul
  -> Stack unit
    (requires fun h -> live h c /\ live h n /\ live h carry /\ disjoint c n)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer carry) (loc_buffer c)) h0 h1)
let mont_reduction_ nLen rLen c n nInv_u64 carry =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_union (loc_buffer carry) (loc_buffer c)) h0 h1 in
  Lib.Loops.for 0ul rLen inv
  (fun i ->
    carry.(0ul) <- u64 0;
    mont_reduction_f nLen rLen c n nInv_u64 carry i
  )

val mont_reduction_a:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> c:lbignum (nLen +. rLen)
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> Stack unit
    (requires fun h -> live h c /\ live h n /\  disjoint c n)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer c) h0 h1)
[@"c_inline"]
let mont_reduction_a nLen rLen c n nInv_u64 =
  push_frame ();
  let carry = create 1ul (u64 0) in
  mont_reduction_ nLen rLen c n nInv_u64 carry;
  pop_frame ()

val mont_reduction:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> c:lbignum (nLen +. nLen)
  -> tmp:lbignum (nLen +. rLen)
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h n /\ live h c /\ live h tmp /\ live h res /\
      disjoint tmp n /\ disjoint tmp c /\ disjoint res tmp)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer res) (loc_buffer tmp)) h0 h1)
[@"c_inline"]
let mont_reduction nLen rLen n nInv_u64 c tmp res =
  let nLen2 = nLen +. nLen in
  let tmp1 = sub tmp 0ul nLen2 in
  copy tmp1 nLen2 c;
  tmp.(nLen2) <- u64 0;
  mont_reduction_a nLen rLen tmp n nInv_u64;
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp1 = sub tmp rLen nLen in
  copy res nLen tmp1

val to_mont:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> st_kara:lbignum (nLen +. nLen +. 4ul *. pow2_i)
  -> aM:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h n /\ live h r2 /\ live h a /\ live h aM /\ live h st_kara /\
      disjoint st_kara a /\ disjoint st_kara r2 /\ disjoint st_kara n /\
      disjoint aM st_kara /\ disjoint st_kara aM)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer aM) (loc_buffer st_kara)) h0 h1)
[@"c_inline"]
let to_mont nLen rLen pow2_i n nInv_u64 r2 a st_kara aM =
  let cLen = nLen +. nLen in
  let stLen = cLen +. 4ul *. pow2_i in
  let c = sub st_kara 0ul cLen in
  karatsuba pow2_i nLen a r2 st_kara; // c = a * r2
  let tmp = sub st_kara cLen (nLen +. rLen) in
  mont_reduction nLen rLen n nInv_u64 c tmp aM // aM = c % n

val from_mont:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum nLen
  -> tmp:lbignum (nLen +. rLen)
  -> a:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h n /\ live h a /\ live h aM /\ live h tmp /\
      disjoint tmp n /\ disjoint aM tmp /\ disjoint a tmp)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer a) (loc_buffer tmp)) h0 h1)
[@"c_inline"]
let from_mont nLen rLen pow2_i n nInv_u64 aM tmp a =
  let tmpLen = nLen +. rLen in
  memset tmp (u64 0) tmpLen;
  let tmp1 = sub tmp 0ul nLen in
  copy tmp1 nLen aM;
  mont_reduction_a nLen rLen tmp n nInv_u64;
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp1 = sub tmp rLen nLen in
  copy a nLen tmp1
