module Hacl.Bignum.Montgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum
open Hacl.Bignum.Base
open Hacl.Bignum.Addition
open Hacl.Bignum.Multiplication

module ST = FStar.HyperStack.ST


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val mod_inv_u64_:
    alpha:uint64
  -> beta:uint64
  -> uv:lbignum 2ul ->
  Stack unit
  (requires fun h -> live h uv)
  (ensures  fun h0 _ h1 -> modifies (loc uv) h0 h1)

let mod_inv_u64_ alpha beta uv =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc uv) h0 h1 in
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


val mod_inv_u64: n0:uint64 ->
  Stack uint64
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> modifies0 h0 h1)

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


//res = res + limb * bn * beta_j
inline_for_extraction noextract
val bn_mult_by_limb_addj_add:
    aLen:size_t
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_t
  -> resLen:size_t{v aLen + v j < v resLen}
  -> res:lbignum resLen
  -> carry:lbignum 1ul ->
  Stack uint64
  (requires fun h ->
    live h a /\ live h res /\ live h carry /\
    disjoint res a /\ disjoint res carry)
  (ensures  fun h0 _ h1 -> modifies (loc carry |+| loc res) h0 h1)

let bn_mult_by_limb_addj_add aLen a l j resLen res carry =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc carry |+| loc res) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let ij = i +. j in
    let res_ij = res.(ij) in
    let c, res_ij = mul_carry_add_u64 a.(i) l carry.(0ul) res_ij in
    carry.(0ul) <- c;
    res.(ij) <- res_ij
  );
  let res1Len = resLen -. (aLen +. j) in
  let res1 = sub res (aLen +. j) res1Len in
  bn_add res1Len res1 1ul carry res1


inline_for_extraction noextract
val mont_reduction_f:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen <= max_size_t}
  -> c:lbignum (nLen +! rLen)
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> carry:lbignum 1ul
  -> i:size_t{v i < v rLen} ->
  Stack unit
  (requires fun h ->
    live h c /\ live h n /\ live h carry /\
    disjoint c n /\ disjoint c carry)
  (ensures  fun h0 _ h1 -> modifies (loc carry |+| loc c) h0 h1)

let mont_reduction_f nLen rLen c n nInv_u64 carry i =
  let ci = c.(i) in
  let qi = nInv_u64 *. ci in
  let _ = bn_mult_by_limb_addj_add nLen n qi i (nLen +. rLen) c carry in ()


inline_for_extraction noextract
val mont_reduction_:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen <= max_size_t}
  -> c:lbignum (nLen +! rLen)
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> carry:lbignum 1ul ->
  Stack unit
  (requires fun h ->
    live h c /\ live h n /\ live h carry /\
    disjoint c n /\ disjoint c carry)
  (ensures  fun h0 _ h1 -> modifies (loc carry |+| loc c) h0 h1)

let mont_reduction_ nLen rLen c n nInv_u64 carry =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc carry |+| loc c) h0 h1 in
  Lib.Loops.for 0ul rLen inv
  (fun i ->
    carry.(0ul) <- u64 0;
    mont_reduction_f nLen rLen c n nInv_u64 carry i
  )


val mont_reduction_a:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen <= max_size_t}
  -> c:lbignum (nLen +! rLen)
  -> n:lbignum nLen
  -> nInv_u64:uint64 ->
  Stack unit
  (requires fun h -> live h c /\ live h n /\  disjoint c n)
  (ensures  fun h0 _ h1 -> modifies (loc c) h0 h1)

[@"c_inline"]
let mont_reduction_a nLen rLen c n nInv_u64 =
  push_frame ();
  let carry = create 1ul (u64 0) in
  mont_reduction_ nLen rLen c n nInv_u64 carry;
  pop_frame ()


val mont_reduction:
    nLen:size_t
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> c:lbignum (nLen +! nLen)
  -> tmp:lbignum (nLen +! rLen)
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h c /\ live h tmp /\ live h res /\
    disjoint tmp n /\ disjoint tmp c /\ disjoint res tmp /\
    0 < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc tmp) h0 h1 /\
    bn_v h1 res % bn_v h0 n == bn_v h0 c / pow2 (64 * v rLen) % bn_v h0 n)

[@"c_inline"]
let mont_reduction nLen rLen n nInv_u64 c tmp res =
  let nLen2 = nLen +! nLen in
  let tmp1 = sub tmp 0ul nLen2 in
  copy tmp1 c;
  tmp.(nLen2) <- u64 0;
  mont_reduction_a nLen rLen tmp n nInv_u64;
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp1 = sub tmp rLen nLen in
  copy res tmp1;
  admit()


val to_mont:
    nLen:size_t{v nLen > 0}
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> aM:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h r2 /\ live h a /\ live h aM /\
    disjoint a r2 /\
    0 < bn_v h n /\ bn_v h r2 == pow2 (2 * 64 * v rLen) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    bn_v h1 aM % bn_v h0 n == bn_v h0 a * pow2 (64 * v rLen) % bn_v h0 n)

[@"c_inline"]
let to_mont nLen rLen n nInv_u64 r2 a aM =
  push_frame ();
  let cLen = nLen +! nLen in
  let tmpLen = nLen +! rLen in
  let c = create cLen (u64 0) in
  let tmp = create tmpLen (u64 0) in
  bn_mul nLen a nLen r2 c; // c = a * r2
  mont_reduction nLen rLen n nInv_u64 c tmp aM; // aM = c % n
  admit();
  pop_frame ()


val from_mont:
    nLen:size_t{v nLen > 0}
  -> rLen:size_t{v nLen < v rLen /\ v nLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum nLen
  -> a:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h aM /\
    0 < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    bn_v h1 a == bn_v h0 aM / pow2 (64 * v rLen) % bn_v h0 n)

[@"c_inline"]
let from_mont nLen rLen n nInv_u64 aM a =
  push_frame ();
  let tmpLen = nLen +! rLen in
  let tmp = create tmpLen (u64 0) in
  update_sub tmp 0ul nLen aM;
  mont_reduction_a nLen rLen tmp n nInv_u64;
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  copy a (sub tmp rLen nLen);
  admit();
  pop_frame ()
