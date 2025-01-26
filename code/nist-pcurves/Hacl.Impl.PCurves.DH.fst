module Hacl.Impl.PCurves.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Scalar
open Hacl.Impl.PCurves.Point
open Hacl.Impl.PCurves.PointMul

module S = Spec.PCurves
module PP = Hacl.Impl.PCurves.PrecompTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
let ecp256dh_i {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| o:order_ops |} {| curve_inv_sqrt|} {| point_ops |} {| PP.precomp_tables |} {| pm:point_mul_ops |} public_key private_key =
  push_frame ();
  let tmp = create (4ul *! cp.bn_limbs) (u64 0) in
  let sk = sub tmp 0ul cp.bn_limbs in
  let pk = sub tmp cp.bn_limbs (3ul *! cp.bn_limbs) in

  let is_sk_valid = o.load_qelem_conditional sk private_key in
  pm.point_mul_g pk sk;
  point_store public_key pk;
  pop_frame ();
  Hacl.Bignum.Base.unsafe_bool_of_limb is_sk_valid


inline_for_extraction noextract
val ecp256dh_r_ {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|}  {| point_ops |} {| PP.precomp_tables |} {| point_mul_ops |}:
  is_pk_valid:bool -> ss:lbuffer uint8 (2ul *! size cp.bytes) -> pk:point -> sk:felem -> Stack unit
  (requires fun h ->
    live h ss /\ live h pk /\ live h sk /\
    disjoint ss pk /\ disjoint ss sk /\ disjoint pk sk /\
    as_nat h sk < S.order /\ (is_pk_valid ==> point_inv h pk))
  (ensures fun  h0 _ h1 -> modifies (loc ss) h0 h1 /\
    as_seq h1 ss == (if is_pk_valid
    then S.point_store (S.point_mul (as_nat h0 sk) (from_mont_point (as_point_nat h0 pk)))
    else as_seq h0 ss))

let ecp256dh_r_ {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} {| point_ops |} {| PP.precomp_tables |} {| pm:point_mul_ops |} is_pk_valid ss pk sk =
  push_frame ();
  let ss_proj = create_point #cp in
  if is_pk_valid then begin
    pm.point_mul ss_proj sk pk;
    point_store ss ss_proj end;
  pop_frame ()


[@CInline]
let ecp256dh_r {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| o:order_ops |} {| curve_inv_sqrt|} {| point_ops |} {| PP.precomp_tables |} {| point_mul_ops |} shared_secret their_pubkey private_key =
  push_frame ();
  let open FStar.Mul in
  let tmp = create (4ul *! size cp.bytes) (u64 0) in
  let sk = sub tmp 0ul cp.bn_limbs in
  let pk = sub tmp cp.bn_limbs (3ul *! cp.bn_limbs) in

  let is_pk_valid = load_point_vartime pk their_pubkey in
  let is_sk_valid = o.load_qelem_conditional sk private_key in
  ecp256dh_r_ is_pk_valid shared_secret pk sk;
  pop_frame ();
  Hacl.Bignum.Base.unsafe_bool_of_limb is_sk_valid && is_pk_valid
