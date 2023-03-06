module Hacl.Impl.P256.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Point
open Hacl.Impl.P256.PointMul

module S = Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let ecp256dh_i public_key private_key =
  push_frame ();
  let tmp = create 100ul (u64 0) in
  let pk = create 12ul (u64 0) in

  secretToPublic pk private_key tmp;
  let flag = is_point_at_inf pk in
  aff_store_point public_key (sub pk 0ul 8ul);
  pop_frame ();

  let open Hacl.Impl.P256.RawCmp in
  unsafe_bool_of_u64 flag


inline_for_extraction noextract
val ecp256dh_r_: ss:point -> pk:point -> private_key:lbuffer uint8 32ul -> Stack uint64
  (requires fun h ->
    live h ss /\ live h pk /\ live h private_key /\
    disjoint ss pk /\ disjoint ss private_key /\ disjoint pk private_key /\
    point_inv h pk)
  (ensures fun  h0 flag h1 -> modifies (loc ss |+| loc pk) h0 h1 /\
    as_point_nat h1 ss ==  S.scalar_multiplication (as_seq h0 private_key) (as_point_nat h0 pk) /\
    v flag == (if S.is_point_at_inf (as_point_nat h1 ss) then ones_v U64 else 0))

let ecp256dh_r_ ss pk private_key =
  push_frame ();
  let tmp = create 100ul (u64 0) in
  scalarMultiplication pk ss private_key tmp;
  pop_frame ();
  is_point_at_inf ss


let ecp256dh_r shared_secret their_pubkey private_key =
  push_frame ();
  let ss = create 12ul (u64 0) in
  let pk = create 12ul (u64 0) in
  let is_pk_valid = load_point_vartime pk their_pubkey in

  let flag = if is_pk_valid then ecp256dh_r_ ss pk private_key else u64 0xFFFFFFFFFFFFFFFF in
  aff_store_point shared_secret (sub ss 0ul 8ul);
  pop_frame ();

  let open Hacl.Impl.P256.RawCmp in
  unsafe_bool_of_u64 flag
