module Hacl.Impl.Curve25519.AddAndDouble

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Curve25519.Fields

module ST = FStar.HyperStack.ST

module F51 = Hacl.Impl.Curve25519.Field51
module F64 = Hacl.Impl.Curve25519.Field64

module P = Spec.Curve25519
module S = Hacl.Spec.Curve25519.AddAndDouble

#reset-options "--z3rlimit 150 --max_fuel 1 --using_facts_from '* -FStar.Seq' --record_options"

inline_for_extraction noextract
let point (s:field_spec) = lbuffer (limb s) (nlimb s +! nlimb s)

(* NEEDED ONLY FOR WRAPPERS *)
inline_for_extraction noextract
let point51 = lbuffer uint64 10ul
inline_for_extraction noextract
let point64 = lbuffer uint64 8ul
(* NEEDED ONLY FOR WRAPPERS *)

let get_x #s (p:point s) = gsub p 0ul (nlimb s)
let get_z #s (p:point s) = gsub p (nlimb s) (nlimb s)

let fget_x (#s:field_spec) (h:mem) (p:point s) = feval h (gsub p 0ul (nlimb s))
let fget_z (#s:field_spec) (h:mem) (p:point s) = feval h (gsub p (nlimb s) (nlimb s))
let fget_xz (#s:field_spec) (h:mem) (p:point s) = fget_x h p, fget_z h p

val point_post_sub_t:#s:field_spec -> h:mem -> f:felem s -> Type0
let point_post_sub_t #s h f =
  match s with
  | M51 -> F51.felem_fits h f (9, 10, 9, 9, 9)
  | M64 -> True

val point_post_add_t:#s:field_spec -> h:mem -> f:felem s -> Type0
let point_post_add_t #s h f =
  match s with
  | M51 -> F51.felem_fits h f (2, 4, 2, 2, 2)
  | M64 -> True

val point_add_and_double0:
    #s:field_spec
  -> nq_p1:point s
  -> ab:lbuffer (limb s) (2ul *! nlimb s)
  -> dc:lbuffer (limb s) (2ul *! nlimb s)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h0 nq_p1 /\ live h0 ab /\ live h0 dc /\ live h0 tmp2 /\
      disjoint nq_p1 ab /\ disjoint nq_p1 dc /\ disjoint nq_p1 tmp2 /\
      disjoint ab dc /\ disjoint ab tmp2 /\ disjoint dc tmp2 /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1) /\
      point_post_add_t h0 (gsub ab 0ul (nlimb s)) /\
      point_post_sub_t h0 (gsub ab (nlimb s) (nlimb s)))
    (ensures  fun h0 _ h1 ->
      modifies (loc nq_p1 |+| loc dc |+| loc tmp2) h0 h1 /\
      point_post_add_t h1 (get_x nq_p1) /\ point_post_sub_t h1 (get_z nq_p1) /\
      fget_xz h1 nq_p1 == S.add_and_double1_0 (fget_x h0 ab) (fget_z h0 ab) (fget_xz h0 nq_p1))
[@ Meta.Attribute.inline_ ]
let point_add_and_double0 #s nq_p1 ab dc tmp2 =
  let x3 = sub nq_p1 0ul (nlimb s) in
  let z3 = sub nq_p1 (nlimb s) (nlimb s) in
  let a : felem s = sub ab 0ul (nlimb s) in
  let b : felem s = sub ab (nlimb s) (nlimb s) in
  let d : felem s = sub dc 0ul (nlimb s) in
  let c : felem s = sub dc (nlimb s) (nlimb s) in

  fadd c x3 z3; // c = x3 + z3
  fsub d x3 z3; // d = x3 - z3

  (* CAN RUN IN PARALLEL *)
  //fmul d d a;   // d = da = d * a
  //fmul c c b;   // c = cb = c * b
  fmul2 dc dc ab tmp2;   // d|c = d*a|c*b
  fadd x3 d c;  // x3 = da + cb
  fsub z3 d c  // z3 = da - cb

val point_add_and_double1:
    #s:field_spec
  -> nq:point s
  -> nq_p1:point s
  -> tmp1:lbuffer (limb s) (4ul *! nlimb s)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h0 nq /\ live h0 nq_p1 /\ live h0 tmp1 /\ live h0 tmp2 /\
      disjoint nq nq_p1 /\ disjoint nq tmp1 /\ disjoint nq tmp2 /\
      disjoint nq_p1 tmp1 /\ disjoint nq_p1 tmp2 /\ disjoint tmp1 tmp2 /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      point_post_add_t h0 (gsub tmp1 0ul (nlimb s)) /\
      point_post_sub_t h0 (gsub tmp1 (nlimb s) (nlimb s)) /\
      point_post_add_t h0 (get_x nq_p1) /\ point_post_sub_t h0 (get_z nq_p1))
    (ensures  fun h0 _ h1 ->
      modifies (loc nq |+| loc nq_p1 |+| loc tmp1 |+| loc tmp2) h0 h1 /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      state_inv_t h1 (get_x nq_p1) /\ state_inv_t h1 (get_z nq_p1) /\
      (fget_xz h1 nq, fget_xz h1 nq_p1) ==
	S.add_and_double1_1 (feval h0 (gsub tmp1 0ul (nlimb s)))
	  (feval h0 (gsub tmp1 (nlimb s) (nlimb s))) (fget_xz h0 nq_p1))
[@ Meta.Attribute.inline_ ]
let point_add_and_double1 #s nq nq_p1 tmp1 tmp2 =
  let x2 = sub nq 0ul (nlimb s) in
  let z2 = sub nq (nlimb s) (nlimb s) in
  let x3 = sub nq_p1 0ul (nlimb s) in
  let z3 = sub nq_p1 (nlimb s) (nlimb s) in

  let a : felem s = sub tmp1 0ul (nlimb s) in
  let b : felem s = sub tmp1 (nlimb s) (nlimb s) in
  let d : felem s = sub tmp1 (2ul *! nlimb s) (nlimb s) in
  let c : felem s = sub tmp1 (3ul *! nlimb s) (nlimb s) in

  let ab : felem2 s = sub tmp1 0ul (2ul *! nlimb s) in
  let dc : felem2 s = sub tmp1 (2ul *! nlimb s) (2ul *! nlimb s) in
  (* CAN RUN IN PARALLEL *)
  //fsqr d a;     // d = aa = a^2
  //fsqr c b;     // c = bb = b^2
  fsqr2 dc ab tmp2;     // d|c = aa | bb
  (* CAN RUN IN PARALLEL *)
  //fsqr x3 x3;   // x3 = (da + cb) ^ 2
  //fsqr z3 z3;   // z3 = (da - cb) ^ 2
  fsqr2 nq_p1 nq_p1 tmp2;   // x3|z3 = x3*x3|z3*z3

  copy_felem a c;                           // a = bb
  fsub c d c;   // c = e = aa - bb
  assert_norm (121665 < pow2 17);
  fmul1 b c (u64 121665); // b = e * 121665
  fadd b b d;   // b = (e * 121665) + aa

  (* CAN RUN IN PARALLEL *)
  //fmul x2 d a;  // x2 = aa * bb
  //fmul z2 c b;  // z2 = e * (aa + (e * 121665))
  fmul2 nq dc ab tmp2  // x2|z2 = aa * bb | e * (aa + (e * 121665))

val point_add_and_double:
    #s:field_spec
  -> q:point s
  -> p01_tmp1:lbuffer (limb s) (8ul *! nlimb s)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
    (
      let nq = gsub p01_tmp1 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1 (2ul *! nlimb s) (2ul *! nlimb s) in
      live h0 q /\ live h0 p01_tmp1 /\ live h0 tmp2 /\
      disjoint q p01_tmp1 /\ disjoint q tmp2 /\ disjoint p01_tmp1 tmp2 /\
      state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1)))
    (ensures  fun h0 _ h1 -> (
      let nq = gsub p01_tmp1 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1 (2ul *! nlimb s) (2ul *! nlimb s) in
      modifies (loc p01_tmp1 |+| loc tmp2) h0 h1 /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      state_inv_t h1 (get_x nq_p1) /\ state_inv_t h1 (get_z nq_p1) /\
     (let p2, p3 = P.add_and_double (fget_xz h0 q) (fget_xz h0 nq) (fget_xz h0 nq_p1) in
      fget_xz h1 nq == p2 /\ fget_xz h1 nq_p1 == p3)))
[@ Meta.Attribute.specialize ]
let point_add_and_double #s q p01_tmp1 tmp2 =
  let h0 = ST.get () in
  let nq : point s = sub p01_tmp1 0ul (2ul *! nlimb s) in
  let nq_p1 : point s = sub p01_tmp1 (2ul *! nlimb s) (2ul *! nlimb s) in
  let tmp1 = sub p01_tmp1 (4ul *! nlimb s) (4ul *! nlimb s) in

  let x1 = sub q 0ul (nlimb s) in
  let x2 = sub nq 0ul (nlimb s) in
  let z2 = sub nq (nlimb s) (nlimb s) in
  let z3 = sub nq_p1 (nlimb s) (nlimb s) in

  let a : felem s = sub tmp1 0ul (nlimb s) in
  let b : felem s = sub tmp1 (nlimb s) (nlimb s) in
  let ab : felem2 s = sub tmp1 0ul (2ul *! nlimb s) in
  let dc : felem2 s = sub tmp1 (2ul *! nlimb s) (2ul *! nlimb s) in

  fadd a x2 z2; // a = x2 + z2
  fsub b x2 z2; // b = x2 - z2

  point_add_and_double0 #s nq_p1 ab dc tmp2;
  point_add_and_double1 #s nq nq_p1 tmp1 tmp2;
  fmul z3 z3 x1 tmp2; // z3 = x1 * (da - cb) ^ 2
  S.lemma_add_and_double (fget_xz h0 q) (fget_xz h0 nq) (fget_xz h0 nq_p1)

val point_double:
    #s:field_spec
  -> nq:point s
  -> tmp1:lbuffer (limb s) (4ul *! nlimb s)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h0 nq /\ live h0 tmp1 /\ live h0 tmp2 /\
      disjoint nq tmp1 /\ disjoint nq tmp2 /\ disjoint tmp1 tmp2 /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq))
    (ensures  fun h0 _ h1 ->
      modifies (loc nq |+| loc tmp1 |+| loc tmp2) h0 h1 /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      fget_xz h1 nq == P.double (fget_xz h0 nq))
[@ Meta.Attribute.specialize ]
let point_double #s nq tmp1 tmp2 =
  let x2 = sub nq 0ul (nlimb s) in
  let z2 = sub nq (nlimb s) (nlimb s) in

  let a : felem s = sub tmp1 0ul (nlimb s) in
  let b : felem s = sub tmp1 (nlimb s) (nlimb s) in
  let d : felem s = sub tmp1 (2ul *! nlimb s) (nlimb s) in
  let c : felem s = sub tmp1 (3ul *! nlimb s) (nlimb s) in

  let ab : felem2 s = sub tmp1 0ul (2ul *! nlimb s) in
  let dc : felem2 s = sub tmp1 (2ul *! nlimb s) (2ul *! nlimb s) in
  let h0 = ST.get () in
  assert (gsub nq 0ul (nlimb s) == x2);
  assert (gsub nq (nlimb s) (nlimb s) == z2);
  assert (gsub ab 0ul (nlimb s) == a);
  assert (gsub ab (nlimb s) (nlimb s) == b);
  assert (gsub dc 0ul (nlimb s) == d);
  assert (gsub dc (nlimb s) (nlimb s) == c);

  fadd a x2 z2; // a = x2 + z2
  fsub b x2 z2; // b = x2 - z2

  (* CAN RUN IN PARALLEL *)
  //fsqr d a;     // d = aa = a^2
  //fsqr c b;     // c = bb = b^2
  fsqr2 dc ab tmp2;     // d|c = aa | bb
  copy_felem a c;                           // a = bb
  fsub c d c;   // c = e = aa - bb
  assert_norm (121665 < pow2 17);
  fmul1 b c (u64 121665); // b = e * 121665
  fadd b b d;   // b = (e * 121665) + aa

  (* CAN RUN IN PARALLEL *)
  //fmul x2 d a;  // x2 = aa * bb
  //fmul z2 c b;  // z2 = e * (aa + (e * 121665))
  fmul2 nq dc ab tmp2  // x2|z2 = aa * bb | e * (aa + (e * 121665))
