module Hacl.Impl.K256.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.K256.Field52.Definitions
open Hacl.Impl.K256.Point

module S = Spec.K256
module SL = Spec.K256.Lemmas

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// unfold let precomp_basepoint_table_list: list uint64 = [
//   // P_0
//   u64 0x0; u64 0x0; u64 0x0; u64 0x0; u64 0x0;
//   u64 0x1; u64 0x0; u64 0x0; u64 0x0; u64 0x0;
//   u64 0x0; u64 0x0; u64 0x0; u64 0x0; u64 0x0;
//   // P_1
//   u64 0x2815b16f81798; u64 0xdb2dce28d959f; u64 0xe870b07029bfc; u64 0xbbac55a06295c; u64 0x79be667ef9dc;
//   u64 0x7d08ffb10d4b8; u64 0x48a68554199c4; u64 0xe1108a8fd17b4; u64 0xc4655da4fbfc0; u64 0x483ada7726a3;
//   u64 0x1; u64 0x0; u64 0x0; u64 0x0; u64 0x0;
//   // P_2
//   u64 0x48e044f109fc8; u64 0x373c920774523; u64 0x39ac4b67827eb; u64 0xf9aa5402b9fdc; u64 0xf40af3b6c6fd;
//   u64 0x89164bfadcbdb; u64 0x3e1b1383f85fe; u64 0xf60db4a43bf63; u64 0xc8f76f5fd7e4b; u64 0x56915849f52c;
//   u64 0x6ba5554759a29; u64 0xcdc3eac498b0c; u64 0x31fc97023dc71; u64 0xa307b568a6ad9; u64 0xf8783c53dfb2;
//   // P_3
//   u64 0x743bb790f36b0; u64 0x85fc6b4b9f2d4; u64 0xca8a1c32e8a3a; u64 0x8a2cf6a7671fe; u64 0x60cf61741984;
//   u64 0x7ed686f22d3a4; u64 0xcf01cb6ba7740; u64 0x49580fb29f8d; u64 0x802c4496c6c94; u64 0x884936b7356d;
//   u64 0x8300925d6f1d4; u64 0x890c0c39e497e; u64 0x9a33c7290e5dc; u64 0x8ab5595351ab8; u64 0x5ac0eb0fb539;
//   // P_4
//   u64 0xa8d95e8d08c8; u64 0x424d85dec433d; u64 0xf04fa8fc34e5f; u64 0x14139cb1bf9c7; u64 0x1d743fca4032;
//   u64 0xa9845fe3f605e; u64 0x91fde09e494b2; u64 0xc472eb4ef7b21; u64 0xc0fbe29ead4d6; u64 0x34fb8147eed1;
//   u64 0xac2271100e68d; u64 0x9984e7e4edd6c; u64 0xe67898df910fc; u64 0x1b2c871f6070c; u64 0x81554cf0ba11;
//   // P_5
//   u64 0x7589553034c8c; u64 0xfae143ee6bbd1; u64 0xd2a4dddf72bef; u64 0xf808e1673167d; u64 0x6c31fec38a52;
//   u64 0x415c48ab514d1; u64 0xdd5a8fe6960a; u64 0xcb851560de31c; u64 0xcda57740c3eea; u64 0x995d6e0c6c03;
//   u64 0x3730d5ce6c85d; u64 0x55d61f66e6306; u64 0x4689c998a59d8; u64 0x3ba10c0c653d9; u64 0x5e87c80e6ebc;
//   // P_6
//   u64 0x3b372eb0f81b5; u64 0x8c759d6268fd4; u64 0xb319ed808b9fd; u64 0x38de42e3e7b13; u64 0x500e998c69da;
//   u64 0x701bb58f3bf9b; u64 0x8bfa9947ce5e6; u64 0x9db75c5e83c22; u64 0x991e8c18d4a68; u64 0x85bbc16d25ec;
//   u64 0x9e679560f6767; u64 0xc878c8474b933; u64 0xcf7ac54533c20; u64 0xef22f54742509; u64 0x6f7961ae1d9d;
//   // P_7
//   u64 0x92852b11abe5a; u64 0x4f646416eae4e; u64 0xb639adaa34214; u64 0x18f4c410d3a43; u64 0x10d5ba07117f;
//   u64 0x5ccc4d5223f0c; u64 0x5348c992c9e65; u64 0x9dc603dd22c90; u64 0x5fd882ef1ff18; u64 0x740429e4bdfd;
//   u64 0x49213a87245d0; u64 0x1f235d735b13c; u64 0x5a56659b7d254; u64 0xd6f6f7b4a5eb; u64 0xa1ea9d796daf;
//   // P_8
//   u64 0xd354595e8091c; u64 0x59727a946d712; u64 0x1ad2fd6b09d6c; u64 0xc18040ba67527; u64 0x94e6b56ba0ec;
//   u64 0x80fcb21037704; u64 0x665a87a06743f; u64 0x1cbeb09af2bf3; u64 0x9d72fe7feb032; u64 0xb74df0c21371;
//   u64 0xb17d5ffe6d714; u64 0x1e355dee022fd; u64 0xac21796140533; u64 0xb639a93da6f3d; u64 0xe15a35015997;
//   // P_9
//   u64 0xb9c5b6ef1f43b; u64 0x2a7bc283fc49f; u64 0x88e368394993f; u64 0xed7b8a9e60d3d; u64 0xf721d2dad6f6;
//   u64 0xec454b7860999; u64 0x89673b944d8e0; u64 0x309522ce23a1a; u64 0x5193173cc4dd9; u64 0x9a1facd6b25a;
//   u64 0xad69b0614f7a2; u64 0xb8d1b10c02e19; u64 0xbc2a2c7b66ffb; u64 0xee4bdc91b3aa8; u64 0xa2b275bde29d;
//   // P_10
//   u64 0x31ac94b24208e; u64 0x11aeaf4ece6d; u64 0xa413faa8d7937; u64 0x90d8df1df29ff; u64 0x5f8d622d2557;
//   u64 0x592ce6949080d; u64 0xf125a05cefe03; u64 0x6d0aa60d51e9b; u64 0x4f07f7c3cf9d4; u64 0x4af6e1ccf133;
//   u64 0xf0f95a3be72b8; u64 0xd3f6d52e63a92; u64 0x17d9ecbe226d1; u64 0x6b6af333c989a; u64 0xe625b11d9a14;
//   // P_11
//   u64 0xd154f79d8e341; u64 0x7cc8bb59c85ee; u64 0xa13927fe452be; u64 0x6e08fbee3b; u64 0xd24d031b1185;
//   u64 0x5c715d4620a0b; u64 0xaa5fd2660d143; u64 0x66bc46a0d83d0; u64 0x2c519acec26ae; u64 0x6c3b82462505;
//   u64 0x8b8cbd971ab15; u64 0xe8501868aee69; u64 0xc54addf1d50d; u64 0x4d8da1ea82014; u64 0x56e000de4c56;
//   // P_12
//   u64 0xbc3731f4e710b; u64 0xf5fe753395cd; u64 0x2804f4c0bc49f; u64 0x11ae10debc618; u64 0x4f17b524159f;
//   u64 0xaae89f1f9385d; u64 0x856a1901e3aea; u64 0x2d28d08cc0cec; u64 0x93d8d337da9b; u64 0x5feedb5497d3;
//   u64 0x5d06206f529e1; u64 0x6c479715a827a; u64 0x48a2dd96d0f48; u64 0x3fdeb0c237630; u64 0x1db55c9d4eaa;
//   // P_13
//   u64 0xe0696573c7533; u64 0x63e4658737869; u64 0x2a11f253f4b05; u64 0x229a7e15cdf48; u64 0x3b9f32f54a4f;
//   u64 0x327e4ceccc2ba; u64 0x3e26d2be9d0df; u64 0x82a00f70af042; u64 0x6020d484c25d6; u64 0xe839a854faeb;
//   u64 0x21ded5312b490; u64 0xf1b776c83d9ed; u64 0x41f6a2c735d44; u64 0x7adcc8a05f3b5; u64 0xd926fe353140;
//   // P_14
//   u64 0xc2b376c728ec; u64 0x947782c52046f; u64 0x27ba54a224d00; u64 0x1035e99c0bf5e; u64 0x612ca1b20e84;
//   u64 0x789d7d062632e; u64 0x683f45cb279ba; u64 0x8b8fac6a007b2; u64 0x350c84e93fa4; u64 0x18a55aa52df;
//   u64 0xe94da9625f527; u64 0xd2619ce2f8a88; u64 0x942403888b43e; u64 0x961da5fd1dc90; u64 0x2f1506d7e117;
//   // P_15
//   u64 0x34deee761bce2; u64 0xfb484324815cc; u64 0xcd7cc675d3a1d; u64 0xca0691e2a6447; u64 0xbb6b7f7b8fa2;
//   u64 0x6c53975090d10; u64 0xa14a4124a90d2; u64 0xbb94d4b653242; u64 0x5074f7da14c32; u64 0xec662837477c;
//   u64 0xee9be37d0b9b; u64 0x4fba9fd90713b; u64 0xcc62c6dc14aa4; u64 0x695bf61db25ac; u64 0x36ba954be769
// ]


unfold
let create15 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14:uint64) : list uint64 =
  [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]

let create15_lseq (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14:uint64) : lseq uint64 15 =
  let l = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14] in
  assert_norm (List.Tot.length l = 15);
  Seq.seq_of_list l

val create15_lemma (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14:uint64) :
  Lemma (let s = create15_lseq x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 in
    s.[0] == x0 /\ s.[1] == x1 /\ s.[2] == x2 /\ s.[3] == x3 /\
    s.[4] == x4 /\ s.[5] == x5 /\ s.[6] == x6 /\ s.[7] == x7 /\
    s.[8] == x8 /\ s.[9] == x9 /\ s.[10] == x10 /\ s.[11] == x11 /\
    s.[12] == x12 /\ s.[13] == x13 /\ s.[14] == x14)

let create15_lemma x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =
  Seq.elim_of_list [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]

let pow_base_point (k:nat) =
  LE.pow S.mk_k256_comm_monoid (S.to_aff_point S.g) k

//-----------------------

unfold
let p0_list : list uint64 =
  create15
    (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0)
    (u64 0x1) (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0)
    (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0)

let p0_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p0_list = 15);
  Seq.seq_of_list p0_list

val p0_lemma : unit -> Lemma (point_eval_lseq p0_lseq == S.point_at_inf_c ())
let p0_lemma () =
  create15_lemma
    (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0)
    (u64 0x1) (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0)
    (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0)

val p0_is_pow0_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p0_lseq) == pow_base_point 0)
let p0_is_pow0_lemma () =
  p0_lemma ();
  LE.lemma_pow0 S.mk_k256_comm_monoid (S.to_aff_point S.g)

//-----------------------

unfold
let p1_list : list uint64 =
  create15
  (u64 0x2815b16f81798) (u64 0xdb2dce28d959f) (u64 0xe870b07029bfc) (u64 0xbbac55a06295c) (u64 0x79be667ef9dc)
  (u64 0x7d08ffb10d4b8) (u64 0x48a68554199c4) (u64 0xe1108a8fd17b4) (u64 0xc4655da4fbfc0) (u64 0x483ada7726a3)
  (u64 0x1) (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0)

let p1_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p1_list = 15);
  Seq.seq_of_list p1_list

val p1_lemma : unit -> Lemma (point_eval_lseq p1_lseq == S.g)
let p1_lemma () =
  create15_lemma
  (u64 0x2815b16f81798) (u64 0xdb2dce28d959f) (u64 0xe870b07029bfc) (u64 0xbbac55a06295c) (u64 0x79be667ef9dc)
  (u64 0x7d08ffb10d4b8) (u64 0x48a68554199c4) (u64 0xe1108a8fd17b4) (u64 0xc4655da4fbfc0) (u64 0x483ada7726a3)
  (u64 0x1) (u64 0x0) (u64 0x0) (u64 0x0) (u64 0x0)

val p1_is_pow1_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p1_lseq) == pow_base_point 1)
let p1_is_pow1_lemma () =
  p1_lemma ();
  LE.lemma_pow1 S.mk_k256_comm_monoid (S.to_aff_point S.g)

//-----------------------

unfold
let p2_list : list uint64 =
  create15
    (u64 0x48e044f109fc8) (u64 0x373c920774523) (u64 0x39ac4b67827eb) (u64 0xf9aa5402b9fdc) (u64 0xf40af3b6c6fd)
    (u64 0x89164bfadcbdb) (u64 0x3e1b1383f85fe) (u64 0xf60db4a43bf63) (u64 0xc8f76f5fd7e4b) (u64 0x56915849f52c)
    (u64 0x6ba5554759a29) (u64 0xcdc3eac498b0c) (u64 0x31fc97023dc71) (u64 0xa307b568a6ad9) (u64 0xf8783c53dfb2)

let p2_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p2_list = 15);
  Seq.seq_of_list p2_list

val p2_eval_lemma : unit -> Lemma
  (let x, y, z = point_eval_lseq p2_lseq in
   let qx = 0xf40af3b6c6fdf9aa5402b9fdc39ac4b67827eb373c92077452348e044f109fc8 in
   let qy = 0x56915849f52cc8f76f5fd7e4bf60db4a43bf633e1b1383f85fe89164bfadcbdb in
   let qz = 0xf8783c53dfb2a307b568a6ad931fc97023dc71cdc3eac498b0c6ba5554759a29 in
   x == qx /\ y == qy /\ z == qz)

let p2_eval_lemma () =
  create15_lemma
    (u64 0x48e044f109fc8) (u64 0x373c920774523) (u64 0x39ac4b67827eb) (u64 0xf9aa5402b9fdc) (u64 0xf40af3b6c6fd)
    (u64 0x89164bfadcbdb) (u64 0x3e1b1383f85fe) (u64 0xf60db4a43bf63) (u64 0xc8f76f5fd7e4b) (u64 0x56915849f52c)
    (u64 0x6ba5554759a29) (u64 0xcdc3eac498b0c) (u64 0x31fc97023dc71) (u64 0xa307b568a6ad9) (u64 0xf8783c53dfb2)

val p2_lemma : unit -> Lemma (point_eval_lseq p2_lseq == S.point_add S.g S.g)
let p2_lemma () =
  let qx = 0xf40af3b6c6fdf9aa5402b9fdc39ac4b67827eb373c92077452348e044f109fc8 in
  let qy = 0x56915849f52cc8f76f5fd7e4bf60db4a43bf633e1b1383f85fe89164bfadcbdb in
  let qz = 0xf8783c53dfb2a307b568a6ad931fc97023dc71cdc3eac498b0c6ba5554759a29 in
  let px, py, pz = normalize_term (S.point_add S.g S.g) in
  assert (qx == px /\ qy = py /\ qz = pz);
  p2_eval_lemma ();
  let x, y, z = point_eval_lseq p2_lseq in
  assert (x == qx /\ y == qy /\ z == qz);
  normalize_term_spec (S.point_add S.g S.g);
  assert ((px, py, pz) == S.point_add S.g S.g);
  assert (px = x /\ py = y /\ pz = z);
  assert (point_eval_lseq p2_lseq == S.point_add S.g S.g)

val p2_is_pow2_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p2_lseq) == pow_base_point 2)
let p2_is_pow2_lemma () =
  let g_aff = S.to_aff_point S.g in
  p2_lemma ();
  SL.to_aff_point_add_lemma S.g S.g;
  assert (S.to_aff_point (point_eval_lseq p2_lseq) == S.aff_point_add g_aff g_aff);
  LE.lemma_pow_unfold S.mk_k256_comm_monoid g_aff 2;
  LE.lemma_pow1 S.mk_k256_comm_monoid g_aff;
  assert (pow_base_point 2 == S.aff_point_add g_aff g_aff)

//-----------------------

unfold
let p3_list : list uint64 =
  create15
  (u64 0x743bb790f36b0) (u64 0x85fc6b4b9f2d4) (u64 0xca8a1c32e8a3a) (u64 0x8a2cf6a7671fe) (u64 0x60cf61741984)
  (u64 0x7ed686f22d3a4) (u64 0xcf01cb6ba7740) (u64 0x49580fb29f8d) (u64 0x802c4496c6c94) (u64 0x884936b7356d)
  (u64 0x8300925d6f1d4) (u64 0x890c0c39e497e) (u64 0x9a33c7290e5dc) (u64 0x8ab5595351ab8) (u64 0x5ac0eb0fb539)

let p3_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p3_list = 15);
  Seq.seq_of_list p3_list

val p3_eval_lemma : unit -> Lemma
  (let x, y, z = point_eval_lseq p3_lseq in
  let qx = 0x60cf617419848a2cf6a7671feca8a1c32e8a3a85fc6b4b9f2d4743bb790f36b0 in
  let qy = 0x884936b7356d802c4496c6c94049580fb29f8dcf01cb6ba77407ed686f22d3a4 in
  let qz = 0x5ac0eb0fb5398ab5595351ab89a33c7290e5dc890c0c39e497e8300925d6f1d4 in
   x == qx /\ y == qy /\ z == qz)

let p3_eval_lemma () =
  create15_lemma
  (u64 0x743bb790f36b0) (u64 0x85fc6b4b9f2d4) (u64 0xca8a1c32e8a3a) (u64 0x8a2cf6a7671fe) (u64 0x60cf61741984)
  (u64 0x7ed686f22d3a4) (u64 0xcf01cb6ba7740) (u64 0x49580fb29f8d) (u64 0x802c4496c6c94) (u64 0x884936b7356d)
  (u64 0x8300925d6f1d4) (u64 0x890c0c39e497e) (u64 0x9a33c7290e5dc) (u64 0x8ab5595351ab8) (u64 0x5ac0eb0fb539)

val p3_lemma : unit -> Lemma (point_eval_lseq p3_lseq == S.point_add (point_eval_lseq p2_lseq) S.g)
let p3_lemma () =
  let qx = 0x60cf617419848a2cf6a7671feca8a1c32e8a3a85fc6b4b9f2d4743bb790f36b0 in
  let qy = 0x884936b7356d802c4496c6c94049580fb29f8dcf01cb6ba77407ed686f22d3a4 in
  let qz = 0x5ac0eb0fb5398ab5595351ab89a33c7290e5dc890c0c39e497e8300925d6f1d4 in

  let rx = 0xf40af3b6c6fdf9aa5402b9fdc39ac4b67827eb373c92077452348e044f109fc8 in
  let ry = 0x56915849f52cc8f76f5fd7e4bf60db4a43bf633e1b1383f85fe89164bfadcbdb in
  let rz = 0xf8783c53dfb2a307b568a6ad931fc97023dc71cdc3eac498b0c6ba5554759a29 in

  let px, py, pz = normalize_term (S.point_add (rx, ry, rz) S.g) in
  assert (qx == px /\ qy = py /\ qz = pz);
  p2_eval_lemma (); // assert ((rx, ry, rz) == point_eval_lseq p2_lseq);
  let x, y, z = point_eval_lseq p3_lseq in
  p3_eval_lemma (); // assert (x == qx /\ y == qy /\ z == qz);
  normalize_term_spec (S.point_add (rx, ry, rz) S.g);
  assert ((px, py, pz) == S.point_add (rx, ry, rz) S.g);
  assert (px = x /\ py = y /\ pz = z);
  assert (point_eval_lseq p3_lseq == S.point_add (rx, ry, rz) S.g)

val p3_is_pow3_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p3_lseq) == pow_base_point 3)
let p3_is_pow3_lemma () =
  let g_aff = S.to_aff_point S.g in
  calc (==) {
    S.to_aff_point (point_eval_lseq p3_lseq);
    (==) { p3_lemma () }
    S.to_aff_point (S.point_add (point_eval_lseq p2_lseq) S.g);
    (==) { SL.to_aff_point_add_lemma (point_eval_lseq p2_lseq) S.g }
    S.aff_point_add (S.to_aff_point (point_eval_lseq p2_lseq)) g_aff;
    (==) { p2_is_pow2_lemma () }
    S.aff_point_add (pow_base_point 2) g_aff;
    (==) { LE.lemma_pow1 S.mk_k256_comm_monoid g_aff }
    S.aff_point_add (pow_base_point 2) (pow_base_point 1);
    (==) { LE.lemma_pow_add S.mk_k256_comm_monoid g_aff 2 1 }
    pow_base_point 3;
  }

//-----------------------

unfold
let p4_list : list uint64 =
  create15
  (u64 0xa8d95e8d08c8) (u64 0x424d85dec433d) (u64 0xf04fa8fc34e5f) (u64 0x14139cb1bf9c7) (u64 0x1d743fca4032)
  (u64 0xa9845fe3f605e) (u64 0x91fde09e494b2) (u64 0xc472eb4ef7b21) (u64 0xc0fbe29ead4d6) (u64 0x34fb8147eed1)
  (u64 0xac2271100e68d) (u64 0x9984e7e4edd6c) (u64 0xe67898df910fc) (u64 0x1b2c871f6070c) (u64 0x81554cf0ba11)

let p4_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p4_list = 15);
  Seq.seq_of_list p4_list

assume
val p4_is_pow4_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p4_lseq) == pow_base_point 4)

//-----------------------

unfold
let p5_list : list uint64 =
  create15
  (u64 0x7589553034c8c) (u64 0xfae143ee6bbd1) (u64 0xd2a4dddf72bef) (u64 0xf808e1673167d) (u64 0x6c31fec38a52)
  (u64 0x415c48ab514d1) (u64 0xdd5a8fe6960a) (u64 0xcb851560de31c) (u64 0xcda57740c3eea) (u64 0x995d6e0c6c03)
  (u64 0x3730d5ce6c85d) (u64 0x55d61f66e6306) (u64 0x4689c998a59d8) (u64 0x3ba10c0c653d9) (u64 0x5e87c80e6ebc)

let p5_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p5_list = 15);
  Seq.seq_of_list p5_list

assume
val p5_is_pow5_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p5_lseq) == pow_base_point 5)

//-----------------------

unfold
let p6_list : list uint64 =
  create15
  (u64 0x3b372eb0f81b5) (u64 0x8c759d6268fd4) (u64 0xb319ed808b9fd) (u64 0x38de42e3e7b13) (u64 0x500e998c69da)
  (u64 0x701bb58f3bf9b) (u64 0x8bfa9947ce5e6) (u64 0x9db75c5e83c22) (u64 0x991e8c18d4a68) (u64 0x85bbc16d25ec)
  (u64 0x9e679560f6767) (u64 0xc878c8474b933) (u64 0xcf7ac54533c20) (u64 0xef22f54742509) (u64 0x6f7961ae1d9d)

let p6_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p6_list = 15);
  Seq.seq_of_list p6_list

assume
val p6_is_pow6_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p6_lseq) == pow_base_point 6)

//-----------------------

unfold
let p7_list : list uint64 =
  create15
  (u64 0x92852b11abe5a) (u64 0x4f646416eae4e) (u64 0xb639adaa34214) (u64 0x18f4c410d3a43) (u64 0x10d5ba07117f)
  (u64 0x5ccc4d5223f0c) (u64 0x5348c992c9e65) (u64 0x9dc603dd22c90) (u64 0x5fd882ef1ff18) (u64 0x740429e4bdfd)
  (u64 0x49213a87245d0) (u64 0x1f235d735b13c) (u64 0x5a56659b7d254) (u64 0xd6f6f7b4a5eb) (u64 0xa1ea9d796daf)

let p7_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p7_list = 15);
  Seq.seq_of_list p7_list

assume
val p7_is_pow7_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p7_lseq) == pow_base_point 7)

//-----------------------

unfold
let p8_list : list uint64 =
  create15
  (u64 0xd354595e8091c) (u64 0x59727a946d712) (u64 0x1ad2fd6b09d6c) (u64 0xc18040ba67527) (u64 0x94e6b56ba0ec)
  (u64 0x80fcb21037704) (u64 0x665a87a06743f) (u64 0x1cbeb09af2bf3) (u64 0x9d72fe7feb032) (u64 0xb74df0c21371)
  (u64 0xb17d5ffe6d714) (u64 0x1e355dee022fd) (u64 0xac21796140533) (u64 0xb639a93da6f3d) (u64 0xe15a35015997)

let p8_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p8_list = 15);
  Seq.seq_of_list p8_list

assume
val p8_is_pow8_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p8_lseq) == pow_base_point 8)

//-----------------------

unfold
let p9_list : list uint64 =
  create15
  (u64 0xb9c5b6ef1f43b) (u64 0x2a7bc283fc49f) (u64 0x88e368394993f) (u64 0xed7b8a9e60d3d) (u64 0xf721d2dad6f6)
  (u64 0xec454b7860999) (u64 0x89673b944d8e0) (u64 0x309522ce23a1a) (u64 0x5193173cc4dd9) (u64 0x9a1facd6b25a)
  (u64 0xad69b0614f7a2) (u64 0xb8d1b10c02e19) (u64 0xbc2a2c7b66ffb) (u64 0xee4bdc91b3aa8) (u64 0xa2b275bde29d)

let p9_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p9_list = 15);
  Seq.seq_of_list p9_list

assume
val p9_is_pow9_lemma: unit -> Lemma (S.to_aff_point (point_eval_lseq p9_lseq) == pow_base_point 9)

//-----------------------

unfold
let p10_list : list uint64 =
  create15
  (u64 0x31ac94b24208e) (u64 0x11aeaf4ece6d) (u64 0xa413faa8d7937) (u64 0x90d8df1df29ff) (u64 0x5f8d622d2557)
  (u64 0x592ce6949080d) (u64 0xf125a05cefe03) (u64 0x6d0aa60d51e9b) (u64 0x4f07f7c3cf9d4) (u64 0x4af6e1ccf133)
  (u64 0xf0f95a3be72b8) (u64 0xd3f6d52e63a92) (u64 0x17d9ecbe226d1) (u64 0x6b6af333c989a) (u64 0xe625b11d9a14)

let p10_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p10_list = 15);
  Seq.seq_of_list p10_list

assume
val p10_is_pow10_lemma: unit ->
  Lemma (S.to_aff_point (point_eval_lseq p10_lseq) == pow_base_point 10)

//-----------------------

unfold
let p11_list : list uint64 =
  create15
  (u64 0xd154f79d8e341) (u64 0x7cc8bb59c85ee) (u64 0xa13927fe452be) (u64 0x6e08fbee3b) (u64 0xd24d031b1185)
  (u64 0x5c715d4620a0b) (u64 0xaa5fd2660d143) (u64 0x66bc46a0d83d0) (u64 0x2c519acec26ae) (u64 0x6c3b82462505)
  (u64 0x8b8cbd971ab15) (u64 0xe8501868aee69) (u64 0xc54addf1d50d) (u64 0x4d8da1ea82014) (u64 0x56e000de4c56)

let p11_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p11_list = 15);
  Seq.seq_of_list p11_list

assume
val p11_is_pow11_lemma: unit ->
  Lemma (S.to_aff_point (point_eval_lseq p11_lseq) == pow_base_point 11)

//-----------------------

unfold
let p12_list : list uint64 =
  create15
  (u64 0xbc3731f4e710b) (u64 0xf5fe753395cd) (u64 0x2804f4c0bc49f) (u64 0x11ae10debc618) (u64 0x4f17b524159f)
  (u64 0xaae89f1f9385d) (u64 0x856a1901e3aea) (u64 0x2d28d08cc0cec) (u64 0x93d8d337da9b) (u64 0x5feedb5497d3)
  (u64 0x5d06206f529e1) (u64 0x6c479715a827a) (u64 0x48a2dd96d0f48) (u64 0x3fdeb0c237630) (u64 0x1db55c9d4eaa)

let p12_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p12_list = 15);
  Seq.seq_of_list p12_list

assume
val p12_is_pow12_lemma: unit ->
  Lemma (S.to_aff_point (point_eval_lseq p12_lseq) == pow_base_point 12)

//-----------------------

unfold
let p13_list : list uint64 =
  create15
  (u64 0xe0696573c7533) (u64 0x63e4658737869) (u64 0x2a11f253f4b05) (u64 0x229a7e15cdf48) (u64 0x3b9f32f54a4f)
  (u64 0x327e4ceccc2ba) (u64 0x3e26d2be9d0df) (u64 0x82a00f70af042) (u64 0x6020d484c25d6) (u64 0xe839a854faeb)
  (u64 0x21ded5312b490) (u64 0xf1b776c83d9ed) (u64 0x41f6a2c735d44) (u64 0x7adcc8a05f3b5) (u64 0xd926fe353140)

let p13_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p13_list = 15);
  Seq.seq_of_list p13_list

assume
val p13_is_pow13_lemma: unit ->
  Lemma (S.to_aff_point (point_eval_lseq p13_lseq) == pow_base_point 13)

//-----------------------

unfold
let p14_list : list uint64 =
  create15
  (u64 0xc2b376c728ec) (u64 0x947782c52046f) (u64 0x27ba54a224d00) (u64 0x1035e99c0bf5e) (u64 0x612ca1b20e84)
  (u64 0x789d7d062632e) (u64 0x683f45cb279ba) (u64 0x8b8fac6a007b2) (u64 0x350c84e93fa4) (u64 0x18a55aa52df)
  (u64 0xe94da9625f527) (u64 0xd2619ce2f8a88) (u64 0x942403888b43e) (u64 0x961da5fd1dc90) (u64 0x2f1506d7e117)

let p14_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p14_list = 15);
  Seq.seq_of_list p14_list

assume
val p14_is_pow14_lemma: unit ->
  Lemma (S.to_aff_point (point_eval_lseq p14_lseq) == pow_base_point 14)

//-----------------------

unfold
let p15_list : list uint64 =
  create15
  (u64 0x34deee761bce2) (u64 0xfb484324815cc) (u64 0xcd7cc675d3a1d) (u64 0xca0691e2a6447) (u64 0xbb6b7f7b8fa2)
  (u64 0x6c53975090d10) (u64 0xa14a4124a90d2) (u64 0xbb94d4b653242) (u64 0x5074f7da14c32) (u64 0xec662837477c)
  (u64 0xee9be37d0b9b) (u64 0x4fba9fd90713b) (u64 0xcc62c6dc14aa4) (u64 0x695bf61db25ac) (u64 0x36ba954be769)

let p15_lseq : lseq uint64 15 =
  assert_norm (List.Tot.length p15_list = 15);
  Seq.seq_of_list p15_list

assume
val p15_is_pow15_lemma: unit ->
  Lemma (S.to_aff_point (point_eval_lseq p15_lseq) == pow_base_point 15)

//-----------------------

unfold let precomp_basepoint_table_list: list uint64 =
  normalize_term
  FStar.List.Tot.(
    p0_list @ p1_list @ p2_list @ p3_list
    @ p4_list @ p5_list @ p6_list @ p7_list
    @ p8_list @ p9_list @ p10_list @ p11_list
    @ p12_list @ p13_list @ p14_list @ p15_list)

// unfold let precomp_basepoint_table_list_l: x:list uint64{List.Tot.length x = 240} =
//   assert_norm (List.Tot.length precomp_basepoint_table_list = 240);
//   precomp_basepoint_table_list

//-----------------------

let precomp_basepoint_table_lseq : lseq uint64 240 =
  assert_norm (List.Tot.length precomp_basepoint_table_list = 240);
  Seq.seq_of_list precomp_basepoint_table_list

val precomp_basepoint_table_lseq_lemma: unit -> Lemma
 (sub precomp_basepoint_table_lseq 0 15 == p0_lseq /\
  sub precomp_basepoint_table_lseq 15 15 == p1_lseq /\
  sub precomp_basepoint_table_lseq 30 15 == p2_lseq /\
  sub precomp_basepoint_table_lseq 45 15 == p3_lseq /\
  sub precomp_basepoint_table_lseq 60 15 == p4_lseq /\
  sub precomp_basepoint_table_lseq 75 15 == p5_lseq /\
  sub precomp_basepoint_table_lseq 90 15 == p6_lseq /\
  sub precomp_basepoint_table_lseq 105 15 == p7_lseq /\
  sub precomp_basepoint_table_lseq 120 15 == p8_lseq /\
  sub precomp_basepoint_table_lseq 135 15 == p9_lseq /\
  sub precomp_basepoint_table_lseq 150 15 == p10_lseq /\
  sub precomp_basepoint_table_lseq 165 15 == p11_lseq /\
  sub precomp_basepoint_table_lseq 180 15 == p12_lseq /\
  sub precomp_basepoint_table_lseq 195 15 == p13_lseq /\
  sub precomp_basepoint_table_lseq 210 15 == p14_lseq /\
  sub precomp_basepoint_table_lseq 225 15 == p15_lseq)

let precomp_basepoint_table_lseq_lemma () =
  Seq.elim_of_list precomp_basepoint_table_list;
  Seq.elim_of_list p0_list;
  eq_intro (sub precomp_basepoint_table_lseq 0 15) p0_lseq;
  Seq.elim_of_list p1_list;
  eq_intro (sub precomp_basepoint_table_lseq 15 15) p1_lseq;
  Seq.elim_of_list p2_list;
  eq_intro (sub precomp_basepoint_table_lseq 30 15) p2_lseq;
  Seq.elim_of_list p3_list;
  eq_intro (sub precomp_basepoint_table_lseq 45 15) p3_lseq;
  Seq.elim_of_list p4_list;
  eq_intro (sub precomp_basepoint_table_lseq 60 15) p4_lseq;
  Seq.elim_of_list p5_list;
  eq_intro (sub precomp_basepoint_table_lseq 75 15) p5_lseq;
  Seq.elim_of_list p6_list;
  eq_intro (sub precomp_basepoint_table_lseq 90 15) p6_lseq;
  Seq.elim_of_list p7_list;
  eq_intro (sub precomp_basepoint_table_lseq 105 15) p7_lseq;
  Seq.elim_of_list p8_list;
  eq_intro (sub precomp_basepoint_table_lseq 120 15) p8_lseq;
  Seq.elim_of_list p9_list;
  eq_intro (sub precomp_basepoint_table_lseq 135 15) p9_lseq;
  Seq.elim_of_list p10_list;
  eq_intro (sub precomp_basepoint_table_lseq 150 15) p10_lseq;
  Seq.elim_of_list p11_list;
  eq_intro (sub precomp_basepoint_table_lseq 165 15) p11_lseq;
  Seq.elim_of_list p12_list;
  eq_intro (sub precomp_basepoint_table_lseq 180 15) p12_lseq;
  Seq.elim_of_list p13_list;
  eq_intro (sub precomp_basepoint_table_lseq 195 15) p13_lseq;
  Seq.elim_of_list p14_list;
  eq_intro (sub precomp_basepoint_table_lseq 210 15) p14_lseq;
  Seq.elim_of_list p15_list;
  eq_intro (sub precomp_basepoint_table_lseq 225 15) p15_lseq


unfold
let precomp_table_inv (j:nat{j < 16}) =
  Math.Lemmas.lemma_mult_lt_right 15 j 16;
  Math.Lemmas.lemma_mult_le_right 15 (j + 1) 16;
  let bj = sub precomp_basepoint_table_lseq (j * 15) 15 in
  S.to_aff_point (point_eval_lseq bj) == pow_base_point j


val precomp_basepoint_table_lemma_i: i:nat{i < 16} -> Lemma (precomp_table_inv i)
let precomp_basepoint_table_lemma_i i =
  precomp_basepoint_table_lseq_lemma ();
  match i with
  | 0 -> p0_is_pow0_lemma ()
  | 1 -> p1_is_pow1_lemma ()
  | 2 -> p2_is_pow2_lemma ()
  | 3 -> p3_is_pow3_lemma ()
  | 4 -> p4_is_pow4_lemma ()
  | 5 -> p5_is_pow5_lemma ()
  | 6 -> p6_is_pow6_lemma ()
  | 7 -> p7_is_pow7_lemma ()
  | 8 -> p8_is_pow8_lemma ()
  | 9 -> p9_is_pow9_lemma ()
  | 10 -> p10_is_pow10_lemma ()
  | 11 -> p11_is_pow11_lemma ()
  | 12 -> p12_is_pow12_lemma ()
  | 13 -> p13_is_pow13_lemma ()
  | 14 -> p14_is_pow14_lemma ()
  | 15 -> p15_is_pow15_lemma ()

val precomp_basepoint_table_lemma: unit -> Lemma (forall (i:nat{i < 16}). precomp_table_inv i)
let precomp_basepoint_table_lemma () =
  FStar.Classical.forall_intro precomp_basepoint_table_lemma_i
