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
  let pk = create_point () in

  secretToPublic pk private_key;
  let flag = is_point_at_inf pk in
  aff_store_point public_key (sub pk 0ul 8ul);
  pop_frame ();

  Hacl.Bignum.Base.unsafe_bool_of_limb0 flag


inline_for_extraction noextract
val ecp256dh_r_:
    is_pk_valid:bool
  -> ss:point
  -> pk:point
  -> private_key:lbuffer uint8 32ul ->
  Stack uint64
  (requires fun h ->
    live h ss /\ live h pk /\ live h private_key /\
    disjoint ss pk /\ disjoint ss private_key /\ disjoint pk private_key /\
    (is_pk_valid ==> point_inv h pk) /\ as_point_nat h ss = (0, 0, 0))
  (ensures fun  h0 flag h1 -> modifies (loc ss |+| loc pk) h0 h1 /\
    as_point_nat h1 ss ==
    (if is_pk_valid then S.scalar_multiplication (as_seq h0 private_key) (as_point_nat h0 pk)
    else (0, 0, 0)) /\
    v flag ==
    (if is_pk_valid then (if S.is_point_at_inf (as_point_nat h1 ss) then ones_v U64 else 0)
    else ones_v U64))

let ecp256dh_r_ is_pk_valid ss pk private_key =
  if is_pk_valid then begin
    scalarMultiplication pk ss private_key;
    is_point_at_inf ss end
  else
    ones U64 SEC


let ecp256dh_r shared_secret their_pubkey private_key =
  push_frame ();
  let ss = create_point () in
  let pk = create_point () in
  let is_pk_valid = load_point_vartime pk their_pubkey in
  let flag = ecp256dh_r_ is_pk_valid ss pk private_key in
  aff_store_point shared_secret (sub ss 0ul 8ul);
  pop_frame ();

  Hacl.Bignum.Base.unsafe_bool_of_limb0 flag
