module Hacl.Impl.PCurves.Verify

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Point
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Scalar
open Hacl.Impl.PCurves.PointMul

module BSeq = Lib.ByteSequence

module S = Spec.PCurves
module SL = Spec.PCurves.Lemmas
module SM = Hacl.Spec.PCurves.Montgomery
module QI = Hacl.Impl.PCurves.Qinv
module PP = Hacl.Impl.PCurves.PrecompTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len

inline_for_extraction noextract
val qmul_mont {| c:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|}:
  sinv:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h sinv /\ live h b /\ live h res /\
    disjoint sinv res /\ disjoint b res /\
    as_nat h sinv < S.order /\ as_nat h b < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    as_nat h1 res = (as_nat h0 sinv * SM.from_qmont (as_nat h0 b) * SM.qmont_R_inv) % S.order)


let qmul_mont {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| o:order_ops |} {| curve_inv_sqrt|} sinv b res =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create_felem #cp in
  o.from_qmont tmp b;
  let h1 = ST.get () in
  assert (as_nat h1 tmp == SM.from_qmont (as_nat h0 b));
  o.qmul res sinv tmp;
  let h2 = ST.get () in
  assert (as_nat h2 res = (as_nat h1 sinv * as_nat h1 tmp * SM.qmont_R_inv) % S.order);
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verification_get_u12 {| c:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|}:
  u1:felem -> u2:felem -> r:felem -> s:felem -> z:felem -> Stack unit
  (requires fun h ->
    live h r /\ live h s /\ live h z /\ live h u1 /\ live h u2 /\
    disjoint u1 u2 /\ disjoint u1 z /\ disjoint u1 r /\ disjoint u1 s /\
    disjoint u2 z /\ disjoint u2 r /\ disjoint u2 s /\
    as_nat h s < S.order /\ as_nat h z < S.order /\ as_nat h r < S.order)
  (ensures fun h0 _ h1 -> modifies (loc u1 |+| loc u2) h0 h1 /\
    (let sinv = S.qinv (as_nat h0 s) in
    as_nat h1 u1 == sinv * as_nat h0 z % S.order /\
    as_nat h1 u2 == sinv * as_nat h0 r % S.order))

let ecdsa_verification_get_u12 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} u1 u2 r s z =
  push_frame ();
  let h0 = ST.get () in
  let sinv = create_felem #cp in
  qinv sinv s;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 sinv == S.qinv (qmont_as_nat h0 s));
  //assert (as_nat h2 sinv * SM.qmont_R_inv % S.order ==
    //S.qinv (as_nat h1 sinv * SM.qmont_R_inv % S.order));

  SM.qmont_inv_mul_lemma (as_nat h0 s) (as_nat h1 sinv) (as_nat h0 z);
  SM.qmont_inv_mul_lemma (as_nat h0 s) (as_nat h1 sinv) (as_nat h0 r);
  qmul_mont sinv z u1;
  qmul_mont sinv r u2;
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verify_finv {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|}:
  p:point -> r:felem -> Stack bool
  (requires fun h ->
    live h p /\ live h r /\ disjoint p r /\
    point_inv h p /\ 0 < as_nat h r /\ as_nat h r < S.order)
    //not (S.is_point_at_inf (from_mont_point (as_point_nat h p))))
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    (let (_X, _Y, _Z) = from_mont_point (as_point_nat h0 p) in
     b <==> (S.fmul _X (S.finv _Z) % S.order = as_nat h0 r)))

let ecdsa_verify_finv {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| o:order_ops |} {| curve_inv_sqrt|} p r_q =
  push_frame ();
  let x = create_felem #cp in
  to_aff_point_x x p;
  o.qmod_short x x;
  let res = bn_is_eq_vartime x r_q in
  pop_frame ();
  res


inline_for_extraction noextract
val ecdsa_verification_cmpr {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| o:order_ops |} {| curve_inv_sqrt|} {| point_ops |} {| PP.precomp_tables |} {| pm:point_mul_ops |}:
  r:felem -> pk:point -> u1:felem -> u2:felem -> Stack bool
  (requires fun h ->
    live h r /\ live h pk /\ live h u1 /\ live h u2 /\
    disjoint r u1 /\ disjoint r u2 /\ disjoint r pk /\
    disjoint pk u1 /\ disjoint pk u2 /\
    point_inv h pk /\ as_nat h u1 < S.order /\ as_nat h u2 < S.order /\
    0 < as_nat h r /\ as_nat h r < S.order)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    (let _X, _Y, _Z = S.point_mul_double_g (as_nat h0 u1) (as_nat h0 u2)
      (from_mont_point (as_point_nat h0 pk)) in
    b <==> (if S.is_point_at_inf (_X, _Y, _Z) then false
      else S.fmul _X (S.finv _Z) % S.order = as_nat h0 r)))

val lemma_ecdsa_verification {| cp:S.curve_params |} : p1:S.proj_point -> p2:S.proj_point -> b:bool -> r:nat ->
  Lemma (requires (r > 0 /\ S.to_aff_point p1 == S.to_aff_point p2 /\
                  (let _X2, _Y2, _Z2 = p2 in
                   b = (if S.is_point_at_inf p2 then false else S.fmul _X2 (S.finv _Z2) % S.order = r))))
        (ensures (let _X1, _Y1, _Z1 = p1 in
                   b = (if S.is_point_at_inf p1 then false else S.fmul _X1 (S.finv _Z1) % S.order = r)))

#push-options "--z3rlimit 200"
let lemma_ecdsa_verification p1 p2 b r = 
    let _X1, _Y1, _Z1 = p1 in
    let _X2, _Y2, _Z2 = p2 in
    SL.lemma_aff_is_point_at_inf p1;
    SL.lemma_aff_is_point_at_inf p2;
    if S.is_point_at_inf p1 then (
      assert (_Z1 = 0);
      assert (S.is_aff_point_at_inf (S.to_aff_point p1));
      assert (S.is_aff_point_at_inf (S.to_aff_point p2));
      assert (_Z2 = 0 || (_X2 = 0 && _Y2 = 0));
      if _Z2 = 0  then assert (b = false)
      else (assert (_X2 = 0);
            assert (b = (S.fmul _X2 (S.finv _Z2) % S.order = r));
            assert (b = (0 = r));
            assert (b = false))
    )
    else ()
#pop-options    

#push-options "--z3rlimit 200"
let ecdsa_verification_cmpr {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} {| point_ops |} {| PP.precomp_tables |} {| pm:point_mul_ops |} r pk u1 u2 =
  push_frame ();
  let res = create_point #cp in
  let h0 = ST.get () in
  pm.point_mul_double_g res u1 u2 pk;
  let h1 = ST.get () in
  assert (S.to_aff_point (from_mont_point (as_point_nat h1 res)) ==
    S.to_aff_point (S.point_mul_double_g (as_nat h0 u1) (as_nat h0 u2)
      (from_mont_point (as_point_nat h0 pk))));
  let b = if is_point_at_inf_vartime res then
             false
          else ecdsa_verify_finv res r in
  pop_frame();
  lemma_ecdsa_verification (S.point_mul_double_g (as_nat h0 u1) (as_nat h0 u2) (from_mont_point (as_point_nat h0 pk))) (from_mont_point (as_point_nat h1 res)) b (as_nat h0 r);
  b 
#pop-options 


inline_for_extraction noextract
val load_signature {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} (r_q s_q:felem) (sign_r sign_s:lbytes (size cp.bytes)) : Stack bool
  (requires fun h ->
    live h sign_r /\ live h sign_s /\ live h r_q /\ live h s_q /\
    disjoint r_q s_q /\ disjoint r_q sign_r /\ disjoint r_q sign_s /\
    disjoint s_q sign_r /\ disjoint s_q sign_s)
  (ensures fun h0 res h1 -> modifies (loc r_q |+| loc s_q) h0 h1 /\
   (let r_q_nat = BSeq.nat_from_bytes_be (as_seq h0 sign_r) in
    let s_q_nat = BSeq.nat_from_bytes_be (as_seq h0 sign_s) in
    as_nat h1 r_q = r_q_nat /\ as_nat h1 s_q = s_q_nat /\
    res == (0 < r_q_nat && r_q_nat < S.order && 0 < s_q_nat && s_q_nat < S.order)))

let load_signature {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} r_q s_q sign_r sign_s =
  bn_from_bytes_be r_q sign_r;
  bn_from_bytes_be s_q sign_s;
  let is_r_valid = bn_is_lt_order_and_gt_zero_mask r_q in
  let is_s_valid = bn_is_lt_order_and_gt_zero_mask s_q in
  Hacl.Bignum.Base.unsafe_bool_of_limb is_r_valid &&
  Hacl.Bignum.Base.unsafe_bool_of_limb is_s_valid


inline_for_extraction noextract
val ecdsa_verify_msg_as_qelem {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} {| point_ops |} {| PP.precomp_tables |} {| pm:point_mul_ops |} :
    m_q:felem
  -> public_key:lbuffer uint8 (2ul *. size cp.bytes)
  -> signature_r:lbuffer uint8 (size cp.bytes)
  -> signature_s:lbuffer uint8 (size cp.bytes) ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h signature_r /\ live h signature_s /\ live h m_q /\
    as_nat h m_q < S.order)
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\
    result == S.ecdsa_verify_msg_as_qelem (as_nat h0 m_q)
      (as_seq h0 public_key) (as_seq h0 signature_r) (as_seq h0 signature_s))

let ecdsa_verify_msg_as_qelem {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} {| point_ops |} {| PP.precomp_tables |} {| pm:point_mul_ops |} m_q public_key signature_r signature_s =
  push_frame ();
  let tmp = create (7ul *. cp.bn_limbs) (u64 0) in
  let pk  = sub tmp 0ul (3ul *. cp.bn_limbs) in
  let r_q = sub tmp (3ul *. cp.bn_limbs) cp.bn_limbs in
  let s_q = sub tmp (4ul *. cp.bn_limbs) cp.bn_limbs in
  let u1  = sub tmp (5ul *. cp.bn_limbs) cp.bn_limbs in
  let u2  = sub tmp (6ul *. cp.bn_limbs) cp.bn_limbs in

  let is_pk_valid = load_point_vartime pk public_key in
  let is_rs_valid = load_signature r_q s_q signature_r signature_s in

  let res =
    if not (is_pk_valid && is_rs_valid) then false
    else begin
      ecdsa_verification_get_u12 u1 u2 r_q s_q m_q;
      ecdsa_verification_cmpr r_q pk u1 u2 end in
  pop_frame ();
  res
