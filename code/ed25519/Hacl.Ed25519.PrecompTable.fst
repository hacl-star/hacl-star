module Hacl.Ed25519.PrecompTable

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module LSeq = Lib.Sequence
module LM = Lib.NatMod
module SE = Spec.Exponentiation
module SPT = Hacl.Spec.PrecompBaseTable
module SPT256 = Hacl.Spec.PrecompBaseTable256
module SPTE = Hacl.Spec.Ed25519.PrecompTable
module S = Spec.Ed25519
module SC = Spec.Curve25519

include Hacl.Impl.Ed25519.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let ext_point_to_list p =
  SPTE.ext_point_to_list_lemma p;
  SPTE.ext_point_to_list p

let lemma_refl x =
  SPTE.ext_point_to_list_lemma x

//-----------------

val lemma_is_on_curve: x:SC.elem -> y:SC.elem ->
  Lemma (Spec.Curve25519.(y *% y -% x *% x) == (y * y - x * x) % SC.prime /\
  Spec.Curve25519.(1 +% S.d *% (x *% x) *% (y *% y)) == (1 + S.d * (x * x) * (y * y)) % SC.prime)

let lemma_is_on_curve x y =
  let open Spec.Curve25519 in
  let open Spec.Ed25519 in
  calc (==) {
    y *% y -% x *% x;
    (==) { }
    ((y * y) % prime - (x * x) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (y * y) (- (x * x) % prime) prime }
    (y * y - (x * x) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (y * y) (x * x) prime }
    (y * y - x * x) % prime;
    };

  calc (==) {
    1 +% S.d *% (x *% x) *% (y *% y);
    (==) { }
    (1 + (S.d * (x * x % prime) % prime) * (y * y % prime) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r S.d (x * x) prime }
    (1 + (S.d * (x * x) % prime) * (y * y % prime) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (S.d * (x * x)) (y * y % prime) prime }
    (1 + (S.d * (x * x)) * (y * y % prime) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (S.d * (x * x)) (y * y) prime }
    (1 + (S.d * (x * x)) * (y * y) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r 1 ((S.d * (x * x)) * (y * y)) prime }
    (1 + (S.d * (x * x)) * (y * y)) % prime;
    }

//--------------

inline_for_extraction noextract
let ext_g_pow2_64 : S.ext_point =
  [@inline_let]
  let rX : SC.elem = 0x5a8a5a58bef144743ef0a14ef1bad8b169be613a4f82d2c418c00c5507edf10d in
  [@inline_let]
  let rY : SC.elem = 0x1ad2dd576455f6786b43640245cf64fae933ffc7ecabc74b63ce54790e453f73 in
  [@inline_let]
  let rZ : SC.elem = 0x424da3d215aef3b7967274a7d81d8d30e7a51756922ebd07058c9d04ac8405e0 in
  [@inline_let]
  let rT : SC.elem = 0x75e4cec7f1c8417c2268c6cff4e4f9d94dd599649b949e8e19cf23c11f401586 in
  (rX, rY, rZ, rT)

val lemma_ext_g_pow2_64_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_ed25519_concrete_ops g_c 64 == ext_g_pow2_64)

let lemma_ext_g_pow2_64_eval () =
  let co = S.mk_ed25519_concrete_ops in
  SPT256.exp_pow2_rec_is_exp_pow2 co g_c 64;
  let qX, qY, qZ, qT = normalize_term (SPT256.exp_pow2_rec co g_c 64) in
  normalize_term_spec (SPT256.exp_pow2_rec co g_c 64);
  let rX : SC.elem = 0x5a8a5a58bef144743ef0a14ef1bad8b169be613a4f82d2c418c00c5507edf10d in
  let rY : SC.elem = 0x1ad2dd576455f6786b43640245cf64fae933ffc7ecabc74b63ce54790e453f73 in
  let rZ : SC.elem = 0x424da3d215aef3b7967274a7d81d8d30e7a51756922ebd07058c9d04ac8405e0 in
  let rT : SC.elem = 0x75e4cec7f1c8417c2268c6cff4e4f9d94dd599649b949e8e19cf23c11f401586 in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ /\ qT == rT)


val ext_g_pow2_64_zinv: unit -> Lemma (let (rX, rY, rZ, rT) = ext_g_pow2_64 in
  SC.finv rZ = 0x32435c2ae3ace33871119d9346f332af7d025740cdca88b087ec408e4b7b1c76)

let ext_g_pow2_64_zinv () =
  let rZ = 0x424da3d215aef3b7967274a7d81d8d30e7a51756922ebd07058c9d04ac8405e0 in
  let rZ_comp = normalize_term (LM.pow_mod_ #SC.prime rZ (SC.prime - 2)) in
  normalize_term_spec (LM.pow_mod_ #SC.prime rZ (SC.prime - 2));
  assert_norm (rZ_comp ==
    0x32435c2ae3ace33871119d9346f332af7d025740cdca88b087ec408e4b7b1c76);

  let (_, _, qZ, _) = ext_g_pow2_64 in
  assert (qZ == rZ);
  LM.pow_mod_def #SC.prime rZ (SC.prime - 2)


val lemma_ext_g_pow2_64_point_inv: unit -> Lemma (S.point_inv ext_g_pow2_64)
let lemma_ext_g_pow2_64_point_inv () =
  let open Spec.Curve25519 in
  let open Spec.Ed25519 in
  let rX : SC.elem = 0x5a8a5a58bef144743ef0a14ef1bad8b169be613a4f82d2c418c00c5507edf10d in
  let rY : SC.elem = 0x1ad2dd576455f6786b43640245cf64fae933ffc7ecabc74b63ce54790e453f73 in
  let rZ : SC.elem = 0x424da3d215aef3b7967274a7d81d8d30e7a51756922ebd07058c9d04ac8405e0 in
  let rT : SC.elem = 0x75e4cec7f1c8417c2268c6cff4e4f9d94dd599649b949e8e19cf23c11f401586 in
  let zinv : SC.elem = 0x32435c2ae3ace33871119d9346f332af7d025740cdca88b087ec408e4b7b1c76 in
  ext_g_pow2_64_zinv ();
  let (x, y) = (rX *% zinv, rY *% zinv) in
  assert (x = 0x6222bd88bf2df9d5d44b60cfb4a08a960078db7ed51a35eb3e0b6b8ff4eda202);
  assert (y = 0x325bb42ea4ed025dd6bdaed261b7c4f5410b608ba902b068f1efa5782e45313);
  lemma_is_on_curve x y;
  assert ((y * y - x * x) % SC.prime =
    0x44b4161cc56730b0c4ddd3ee61af107f6ec87d11e0da287cb1dc61a07d10842a);
  assert ((1 + d * (x * x) * (y * y)) % SC.prime =
    0x44b4161cc56730b0c4ddd3ee61af107f6ec87d11e0da287cb1dc61a07d10842a);
  assert (S.is_on_curve (x, y));
  assert (rX *% rY *% zinv =
    0x75e4cec7f1c8417c2268c6cff4e4f9d94dd599649b949e8e19cf23c11f401586);
  assert (S.is_ext ext_g_pow2_64)


inline_for_extraction noextract
let ext_g_pow2_64_c : S.ext_point_c =
  lemma_ext_g_pow2_64_point_inv ();
  ext_g_pow2_64


inline_for_extraction noextract
let ext_g_pow2_128 : S.ext_point =
  [@inline_let]
  let rX : SC.elem = 0x38569441a1f5cd408a120bf398c05f4d98921fc59796c50c2af9fb1690e8727e in
  [@inline_let]
  let rY : SC.elem = 0x0a97dfad58fa26197529d9296502368db1c0513ba4c45512f239db96f78d2e7c in
  [@inline_let]
  let rZ : SC.elem = 0x78d98ebac33bd94604a2ce24527eb73c2cba4d3b1e5f55b8444bb5e513a54540 in
  [@inline_let]
  let rT : SC.elem = 0x3dc4d80a0c809ab67253c9cae46b0a2fdbfca8ca0f515475b21d1e95fb8d9add in
  (rX, rY, rZ, rT)

val lemma_ext_g_pow2_128_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_ed25519_concrete_ops ext_g_pow2_64_c 64 == ext_g_pow2_128)

let lemma_ext_g_pow2_128_eval () =
  let co = S.mk_ed25519_concrete_ops in
  SPT256.exp_pow2_rec_is_exp_pow2 co ext_g_pow2_64_c 64;
  let qX, qY, qZ, qT = normalize_term (SPT256.exp_pow2_rec co ext_g_pow2_64_c 64) in
  normalize_term_spec (SPT256.exp_pow2_rec co ext_g_pow2_64_c 64);
  let rX : SC.elem = 0x38569441a1f5cd408a120bf398c05f4d98921fc59796c50c2af9fb1690e8727e in
  let rY : SC.elem = 0x0a97dfad58fa26197529d9296502368db1c0513ba4c45512f239db96f78d2e7c in
  let rZ : SC.elem = 0x78d98ebac33bd94604a2ce24527eb73c2cba4d3b1e5f55b8444bb5e513a54540 in
  let rT : SC.elem = 0x3dc4d80a0c809ab67253c9cae46b0a2fdbfca8ca0f515475b21d1e95fb8d9add in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ /\ qT == rT)


val ext_g_pow2_128_zinv: unit -> Lemma (let (rX, rY, rZ, rT) = ext_g_pow2_128 in
  SC.finv rZ = 0xa908d480f92385648adf4303f41d185348ebd63cea140b01be3c2e3b13b378)

let ext_g_pow2_128_zinv () =
  let rZ = 0x78d98ebac33bd94604a2ce24527eb73c2cba4d3b1e5f55b8444bb5e513a54540 in
  let rZ_comp = normalize_term (LM.pow_mod_ #SC.prime rZ (SC.prime - 2)) in
  normalize_term_spec (LM.pow_mod_ #SC.prime rZ (SC.prime - 2));
  assert_norm (rZ_comp ==
    0xa908d480f92385648adf4303f41d185348ebd63cea140b01be3c2e3b13b378);

  let (_, _, qZ, _) = ext_g_pow2_128 in
  assert (qZ == rZ);
  LM.pow_mod_def #SC.prime rZ (SC.prime - 2)


val lemma_ext_g_pow2_128_point_inv: unit -> Lemma (S.point_inv ext_g_pow2_128)
let lemma_ext_g_pow2_128_point_inv () =
  let open Spec.Curve25519 in
  let open Spec.Ed25519 in
  let rX : SC.elem = 0x38569441a1f5cd408a120bf398c05f4d98921fc59796c50c2af9fb1690e8727e in
  let rY : SC.elem = 0x0a97dfad58fa26197529d9296502368db1c0513ba4c45512f239db96f78d2e7c in
  let rZ : SC.elem = 0x78d98ebac33bd94604a2ce24527eb73c2cba4d3b1e5f55b8444bb5e513a54540 in
  let rT : SC.elem = 0x3dc4d80a0c809ab67253c9cae46b0a2fdbfca8ca0f515475b21d1e95fb8d9add in
  let zinv : SC.elem = 0xa908d480f92385648adf4303f41d185348ebd63cea140b01be3c2e3b13b378 in
  ext_g_pow2_128_zinv ();
  let (x, y) = (rX *% zinv, rY *% zinv) in
  assert (x = 0x4c27afff3c45f32c952d3984e14e29a098e685c9c2e723e5fc8047ae60b7e824);
  assert (y = 0x5f2c99e6526dc87d95f11eb626c29c3a90d0be1e51a4c49e5bbabd114bf5a66b);
  lemma_is_on_curve x y;
  assert ((y * y - x * x) % SC.prime =
    0x1a6a9dfe3e20bc6d73e5c689df4c1b7d21d6a7d878feb81680f0e5cb6e31ea55);
  assert ((1 + d * (x * x) * (y * y)) % SC.prime =
    0x1a6a9dfe3e20bc6d73e5c689df4c1b7d21d6a7d878feb81680f0e5cb6e31ea55);
  assert (S.is_on_curve (x, y));
  assert (rX *% rY *% zinv =
    0x3dc4d80a0c809ab67253c9cae46b0a2fdbfca8ca0f515475b21d1e95fb8d9add);
  assert (S.is_ext ext_g_pow2_128)


inline_for_extraction noextract
let ext_g_pow2_128_c : S.ext_point_c =
  lemma_ext_g_pow2_128_point_inv ();
  ext_g_pow2_128


inline_for_extraction noextract
let ext_g_pow2_192 : S.ext_point =
  [@inline_let]
  let rX : SC.elem = 0x59a2726d1a927e56005542ff7c0dded153e9146340a7ba261e0403afbd77ba7d in
  [@inline_let]
  let rY : SC.elem = 0x09344b8ad2982520f18314ea851cebe018a16987ad52191e466d5c1d19f5096d in
  [@inline_let]
  let rZ : SC.elem = 0x7d0300628a3869589b68ed3d9c968775e69a9e2a7c7913184c5af18b60a3effb in
  [@inline_let]
  let rT : SC.elem = 0x4ba921103721bfbb5070816bf7abc2fcb5fb2e653f32d7188e21c4170e2d4e01 in
  (rX, rY, rZ, rT)

val lemma_ext_g_pow2_192_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_ed25519_concrete_ops ext_g_pow2_128_c 64 == ext_g_pow2_192)

let lemma_ext_g_pow2_192_eval () =
  let co = S.mk_ed25519_concrete_ops in
  SPT256.exp_pow2_rec_is_exp_pow2 co ext_g_pow2_128_c 64;
  let qX, qY, qZ, qT = normalize_term (SPT256.exp_pow2_rec co ext_g_pow2_128_c 64) in
  normalize_term_spec (SPT256.exp_pow2_rec co ext_g_pow2_128_c 64);
  let rX : SC.elem = 0x59a2726d1a927e56005542ff7c0dded153e9146340a7ba261e0403afbd77ba7d in
  let rY : SC.elem = 0x09344b8ad2982520f18314ea851cebe018a16987ad52191e466d5c1d19f5096d in
  let rZ : SC.elem = 0x7d0300628a3869589b68ed3d9c968775e69a9e2a7c7913184c5af18b60a3effb in
  let rT : SC.elem = 0x4ba921103721bfbb5070816bf7abc2fcb5fb2e653f32d7188e21c4170e2d4e01 in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ /\ qT == rT)


val ext_g_pow2_192_zinv: unit -> Lemma (let (rX, rY, rZ, rT) = ext_g_pow2_192 in
  SC.finv rZ = 0x2972deff9b37f94926b9a4d6b37f37d190689259040e63ed0da418e98c52b9d4)

let ext_g_pow2_192_zinv () =
  let rZ = 0x7d0300628a3869589b68ed3d9c968775e69a9e2a7c7913184c5af18b60a3effb in
  let rZ_comp = normalize_term (LM.pow_mod_ #SC.prime rZ (SC.prime - 2)) in
  normalize_term_spec (LM.pow_mod_ #SC.prime rZ (SC.prime - 2));
  assert_norm (rZ_comp ==
    0x2972deff9b37f94926b9a4d6b37f37d190689259040e63ed0da418e98c52b9d4);

  let (_, _, qZ, _) = ext_g_pow2_192 in
  assert (qZ == rZ);
  LM.pow_mod_def #SC.prime rZ (SC.prime - 2)


val lemma_ext_g_pow2_192_point_inv: unit -> Lemma (S.point_inv ext_g_pow2_192)
let lemma_ext_g_pow2_192_point_inv () =
  let open Spec.Curve25519 in
  let open Spec.Ed25519 in
  let rX : SC.elem = 0x59a2726d1a927e56005542ff7c0dded153e9146340a7ba261e0403afbd77ba7d in
  let rY : SC.elem = 0x09344b8ad2982520f18314ea851cebe018a16987ad52191e466d5c1d19f5096d in
  let rZ : SC.elem = 0x7d0300628a3869589b68ed3d9c968775e69a9e2a7c7913184c5af18b60a3effb in
  let rT : SC.elem = 0x4ba921103721bfbb5070816bf7abc2fcb5fb2e653f32d7188e21c4170e2d4e01 in
  let zinv : SC.elem = 0x2972deff9b37f94926b9a4d6b37f37d190689259040e63ed0da418e98c52b9d4 in
  ext_g_pow2_192_zinv ();
  let (x, y) = (rX *% zinv, rY *% zinv) in
  assert (x = 0x1bc7af1e38185e7c2d8d04371c7e177d7a9ddee1b81d7d26db7ad644c7dad28d);
  assert (y = 0x61d909d855661f2f7a5eef87795dc0491d027e12631b270fcaf2f65900314833);
  lemma_is_on_curve x y;
  assert ((y * y - x * x) % SC.prime =
    0x17b3d90b42ff679b6cc94130e36b67e6a1fe8292c22f4e6f1cdff4a37fecafd8);
  assert ((1 + d * (x * x) * (y * y)) % SC.prime =
    0x17b3d90b42ff679b6cc94130e36b67e6a1fe8292c22f4e6f1cdff4a37fecafd8);
  assert (S.is_on_curve (x, y));
  assert (rX *% rY *% zinv =
    0x4ba921103721bfbb5070816bf7abc2fcb5fb2e653f32d7188e21c4170e2d4e01);
  assert (S.is_ext ext_g_pow2_192)


inline_for_extraction noextract
let ext_g_pow2_192_c : S.ext_point_c =
  lemma_ext_g_pow2_192_point_inv ();
  ext_g_pow2_192


inline_for_extraction noextract
let ext_g_pow2_64_list : SPTE.point_list =
  normalize_term (SPTE.ext_point_to_list ext_g_pow2_64_c)

inline_for_extraction noextract
let ext_g_pow2_128_list : SPTE.point_list =
  normalize_term (SPTE.ext_point_to_list ext_g_pow2_128_c)

inline_for_extraction noextract
let ext_g_pow2_192_list : SPTE.point_list =
  normalize_term (SPTE.ext_point_to_list ext_g_pow2_192_c)


let ext_g_pow2_64_lseq : LSeq.lseq uint64 20 =
  normalize_term_spec (SPTE.ext_point_to_list ext_g_pow2_64_c);
  Seq.seq_of_list ext_g_pow2_64_list

let ext_g_pow2_128_lseq : LSeq.lseq uint64 20 =
  normalize_term_spec (SPTE.ext_point_to_list ext_g_pow2_128_c);
  Seq.seq_of_list ext_g_pow2_128_list

let ext_g_pow2_192_lseq : LSeq.lseq uint64 20 =
  normalize_term_spec (SPTE.ext_point_to_list ext_g_pow2_192_c);
  Seq.seq_of_list ext_g_pow2_192_list


val ext_g_pow2_64_lemma: unit ->
  Lemma (S.to_aff_point ext_g_pow2_64_c == pow_point (pow2 64) g_aff)

let ext_g_pow2_64_lemma () =
  lemma_ext_g_pow2_64_eval ();
  SPT256.a_pow2_64_lemma S.mk_ed25519_concrete_ops S.g


val ext_g_pow2_128_lemma: unit ->
  Lemma (S.to_aff_point ext_g_pow2_128_c == pow_point (pow2 128) g_aff)

let ext_g_pow2_128_lemma () =
  lemma_ext_g_pow2_128_eval ();
  lemma_ext_g_pow2_64_eval ();
  SPT256.a_pow2_128_lemma S.mk_ed25519_concrete_ops S.g


val ext_g_pow2_192_lemma: unit ->
  Lemma (S.to_aff_point ext_g_pow2_192 == pow_point (pow2 192) g_aff)

let ext_g_pow2_192_lemma () =
  lemma_ext_g_pow2_192_eval ();
  lemma_ext_g_pow2_128_eval ();
  lemma_ext_g_pow2_64_eval ();
  SPT256.a_pow2_192_lemma S.mk_ed25519_concrete_ops S.g


let ext_g_pow2_64_lseq_lemma () =
  normalize_term_spec (SPTE.ext_point_to_list ext_g_pow2_64_c);
  ext_g_pow2_64_lemma ();
  SPTE.ext_point_to_list_lemma ext_g_pow2_64_c


let ext_g_pow2_128_lseq_lemma () =
  normalize_term_spec (SPTE.ext_point_to_list ext_g_pow2_128_c);
  ext_g_pow2_128_lemma ();
  SPTE.ext_point_to_list_lemma ext_g_pow2_128_c


let ext_g_pow2_192_lseq_lemma () =
  normalize_term_spec (SPTE.ext_point_to_list ext_g_pow2_192_c);
  ext_g_pow2_192_lemma ();
  SPTE.ext_point_to_list_lemma ext_g_pow2_192_c


let mk_ext_g_pow2_64 () =
  createL ext_g_pow2_64_list

let mk_ext_g_pow2_128 () =
  createL ext_g_pow2_128_list

let mk_ext_g_pow2_192 () =
  createL ext_g_pow2_192_list


///  window size = 4; precomputed table = [[0]G, [1]G, ..., [15]G]

inline_for_extraction noextract
let precomp_basepoint_table_list_w4: x:list uint64{FStar.List.Tot.length x = 320} =
  normalize_term (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15)


let precomp_basepoint_table_lseq_w4 : LSeq.lseq uint64 320 =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15);
  Seq.seq_of_list precomp_basepoint_table_list_w4


let precomp_basepoint_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15);
  SPT.precomp_base_table_lemma
    mk_ed25519_precomp_base_table g_c 16 precomp_basepoint_table_lseq_w4


let precomp_basepoint_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_basepoint_table_lseq_w4 /\ recallable x} =
  createL_global precomp_basepoint_table_list_w4


///  window size = 4; precomputed table = [[0]([pow2 64]G), [1]([pow2 64]G), ..., [15]([pow2 64]G)]

inline_for_extraction noextract
let precomp_g_pow2_64_table_list_w4: x:list uint64{FStar.List.Tot.length x = 320} =
  normalize_term (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_64_c 15)

let precomp_g_pow2_64_table_lseq_w4 : LSeq.lseq uint64 320 =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_64_c 15);
  Seq.seq_of_list precomp_g_pow2_64_table_list_w4

let precomp_g_pow2_64_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_64_c 15);
  SPT.precomp_base_table_lemma mk_ed25519_precomp_base_table
    ext_g_pow2_64_c 16 precomp_g_pow2_64_table_lseq_w4;
  ext_g_pow2_64_lemma ()

let precomp_g_pow2_64_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_g_pow2_64_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_64_table_list_w4


///  window size = 4; precomputed table = [[0]([pow2 128]G), [1]([pow2 128]G),...,[15]([pow2 128]G)]

inline_for_extraction noextract
let precomp_g_pow2_128_table_list_w4: x:list uint64{FStar.List.Tot.length x = 320} =
  normalize_term (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_128_c 15)

let precomp_g_pow2_128_table_lseq_w4 : LSeq.lseq uint64 320 =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_128_c 15);
  Seq.seq_of_list precomp_g_pow2_128_table_list_w4

let precomp_g_pow2_128_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_128_c 15);
  SPT.precomp_base_table_lemma mk_ed25519_precomp_base_table
    ext_g_pow2_128_c 16 precomp_g_pow2_64_table_lseq_w4;
  ext_g_pow2_128_lemma ()

let precomp_g_pow2_128_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_g_pow2_128_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_128_table_list_w4

///  window size = 4; precomputed table = [[0]([pow2 192]G), [1]([pow2 192]G),...,[15]([pow2 192]G)]

inline_for_extraction noextract
let precomp_g_pow2_192_table_list_w4: x:list uint64{FStar.List.Tot.length x = 320} =
  normalize_term (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_192_c 15)

let precomp_g_pow2_192_table_lseq_w4 : LSeq.lseq uint64 320 =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_192_c 15);
  Seq.seq_of_list precomp_g_pow2_192_table_list_w4

let precomp_g_pow2_192_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table ext_g_pow2_192_c 15);
  SPT.precomp_base_table_lemma mk_ed25519_precomp_base_table
    ext_g_pow2_192_c 16 precomp_g_pow2_64_table_lseq_w4;
  ext_g_pow2_192_lemma ()

let precomp_g_pow2_192_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_g_pow2_192_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_192_table_list_w4

///  window size = 5

inline_for_extraction noextract
let precomp_basepoint_table_list_w5: x:list uint64{FStar.List.Tot.length x = 640} =
  normalize_term (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 31)


let precomp_basepoint_table_lseq_w5 : LSeq.lseq uint64 640 =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 31);
  Seq.seq_of_list precomp_basepoint_table_list_w5

#push-options "--z3rlimit_factor 2"
let precomp_basepoint_table_lemma_w5 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 31);
  SPT.precomp_base_table_lemma
    mk_ed25519_precomp_base_table g_c 32 precomp_basepoint_table_lseq_w5
#pop-options

let precomp_basepoint_table_w5:
  x:glbuffer uint64 640ul{witnessed x precomp_basepoint_table_lseq_w5 /\ recallable x} =
  createL_global precomp_basepoint_table_list_w5
