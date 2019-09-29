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
module S = Hacl.Spec.Bignum.Montgomery
module Loops = Lib.LoopCombinators


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

[@CInline]
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
val mont_reduction_:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> j:size_t{v j < v rLen}
  -> res:lbignum (rLen +! rLen) ->
  Stack unit
  (requires fun h -> live h n /\ live h res /\ disjoint n res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.mont_reduction_ #(v nLen) #(v rLen) (as_seq h0 n) nInv_u64 (v j) (as_seq h0 res))

let mont_reduction_ nLen rLen n nInv_u64 j res =
  push_frame ();
  let qj = nInv_u64 *. res.(j) in
  let res' = sub res j nLen in
  let c = bn_mul_by_limb_addj nLen n qj res' in

  let res' = sub res (j +! nLen) (rLen +! rLen -! j -! nLen) in
  let c = create 1ul c in
  let _ = bn_add (rLen +! rLen -! j -! nLen) res' 1ul c res' in
  pop_frame ();
  admit()


//bn_v h1 res % bn_v h0 n == bn_v h0 c / pow2 (64 * v rLen) % bn_v h0 n)
val mont_reduction:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> c:lbignum (rLen +! rLen)
  -> res:lbignum rLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h c /\ live h res /\
    disjoint res n /\ disjoint res c /\ disjoint n c /\
    0 < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    as_seq h1 res == S.mont_reduction #(v nLen) #(v rLen) (as_seq h0 n) nInv_u64 (as_seq h0 c))

[@CInline]
let mont_reduction nLen rLen n nInv_u64 c res =
  [@ inline_let]
  let spec h = S.mont_reduction_ #(v nLen) #(v rLen) (as_seq h n) nInv_u64 in

  let h0 = ST.get () in
  loop1 h0 rLen c spec
  (fun j ->
    Loops.unfold_repeati (v rLen) (spec h0) (as_seq h0 c) (v j);
    mont_reduction_ nLen rLen n nInv_u64 j c
  );
  copy res (sub c rLen rLen)


// bn_v h1 aM % bn_v h0 n == bn_v h0 a * pow2 (64 * v rLen) % bn_v h0 n
val to_mont:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> aM:lbignum rLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h r2 /\ live h a /\ live h aM /\
    disjoint a r2 /\ disjoint a n /\ disjoint a aM /\
    disjoint n r2 /\ disjoint n aM /\ disjoint r2 aM /\
    0 < bn_v h n /\ bn_v h r2 == pow2 (2 * 64 * v rLen) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    as_seq h1 aM == S.to_mont #(v nLen) #(v rLen) (as_seq h0 n) nInv_u64 (as_seq h0 r2) (as_seq h0 a))

[@CInline]
let to_mont nLen rLen n nInv_u64 r2 a aM =
  push_frame ();
  let tmp = create (rLen +! rLen) (u64 0) in
  let c = sub tmp 0ul (nLen +! nLen) in
  bn_mul nLen a nLen r2 c; // c = a * r2
  mont_reduction nLen rLen n nInv_u64 tmp aM; // aM = c % n
  pop_frame (); admit()


//bn_v h1 a == bn_v h0 aM / pow2 (64 * v rLen) % bn_v h0 n
val from_mont:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum rLen
  -> a:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h aM /\
    disjoint aM a /\ disjoint aM n /\ disjoint a n /\
    0 < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.from_mont #(v nLen) #(v rLen) (as_seq h0 n) nInv_u64 (as_seq h0 aM))

[@CInline]
let from_mont nLen rLen n nInv_u64 aM a =
  push_frame ();
  let tmp = create (rLen +! rLen) (u64 0) in
  update_sub tmp 0ul rLen aM;
  let a' = create rLen (u64 0) in
  mont_reduction nLen rLen n nInv_u64 tmp a';
  copy a (sub a' 0ul nLen);
  pop_frame (); admit()
