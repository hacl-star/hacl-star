module Hacl.Impl.P256.Sign

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Hacl.Spec.P256.Bignum
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.Qinv
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.Point
open Hacl.Impl.P256.PointMul

open Spec.Hash.Definitions
open Hacl.Hash.SHA2

module S = Spec.P256

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"


inline_for_extraction noextract
val ecdsa_signature_step12: alg:S.hash_alg_ecdsa
  -> mLen: size_t {v mLen >= S.min_input_length alg}
  -> m: lbuffer uint8 mLen -> result: felem -> Stack unit
  (requires fun h -> live h m /\ live h result )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    (
      assert_norm (pow2 32 < pow2 61);
      assert_norm (pow2 32 < pow2 125);
      let hashM = S.hash_ecdsa alg (v mLen) (as_seq h0 m) in
      let cutHashM = Lib.Sequence.sub hashM 0 32 in
      as_nat h1 result = nat_from_bytes_be cutHashM % S.order
    )
  )

let ecdsa_signature_step12 alg mLen m result =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame();
    let h0 = ST.get() in
  let sz: FStar.UInt32.t = match alg with | S.NoHash -> mLen | S.Hash a ->  Hacl.Hash.Definitions.hash_len a in
  let mHash = create sz (u8 0) in

  begin
  match alg with
    | S.NoHash -> copy mHash m
    | S.Hash a -> match a with
      |SHA2_256 -> hash_256 m mLen mHash
      |SHA2_384 -> hash_384 m mLen mHash
      |SHA2_512 -> hash_512 m mLen mHash
  end;

  let cutHash = sub mHash (size 0) (size 32) in
  bn_from_bytes_be4 cutHash result;

  let h1 = ST.get() in

  qmod_short result result;

  lemma_core_0 result h1;
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 cutHash);

  pop_frame()

#push-options "--ifuel 1"

inline_for_extraction
val ecdsa_signature_step45: x: felem
  -> k: lbuffer uint8 (size 32)
  -> tempBuffer: lbuffer uint64 (size 100)
  -> Stack uint64
    (requires fun h ->
      live h x /\ live h k /\ live h tempBuffer /\
      LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc k; loc x]
    )
    (ensures fun h0 r h1 ->
      modifies (loc x |+| loc tempBuffer) h0 h1 /\
      as_nat h1 x < S.order /\
      (
	let (rxN, ryN, rzN), _ = S.montgomery_ladder_spec (as_seq h0 k) ((0,0,0), S.base_point) in
	let (xN, _, _) = S.norm_jacob_point (rxN, ryN, rzN) in
	as_nat h1 x == xN % S.order /\
	(
	  if as_nat h1 x = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0
	)
      )
    )

let ecdsa_signature_step45 x k tempBuffer =
  push_frame();
    let result = create (size 12) (u64 0) in
    let tempForNorm = sub tempBuffer (size 0) (size 88) in
    secretToPublicWithoutNorm result k tempBuffer;
    norm_jacob_point_x result x;
    qmod_short x x;
  pop_frame();
    bn_is_zero_mask4 x

#pop-options

val lemma_power_step6: kInv: nat -> Lemma
  (S.qinv (fromDomain_ kInv) == toDomain_ (S.pow kInv (S.order - 2)))

let lemma_power_step6 kInv =
  let a = S.qinv (fromDomain_ kInv) in
  lemmaFromDomain kInv;

  //power_distributivity (kInv * S.modp_inv2_prime (pow2 256) S.order) (S.order - 2) S.order;
  //power_distributivity_2 kInv (S.modp_inv2_prime (pow2 256) S.order % S.order) (S.order - 2);
  lemma_mod_mul_distr_r (S.pow kInv (S.order - 2)) (S.pow (S.modp_inv2_prime (pow2 256) S.order) (S.order - 2)) S.order;

  //lemma_pow_mod_n_is_fpow S.order (pow2 256 % S.order) (S.order - 2);

  let inverse2_256 = 43790243014242295660885426880012836369732278457577312309071968676491870960761 in
  assert_norm(S.modp_inv2_prime (pow2 256) S.order = inverse2_256);
  //lemma_pow_mod_n_is_fpow S.order inverse2_256 (S.order - 2);
  assert_norm(S.exp #S.order inverse2_256 (S.order - 2) == pow2 256 % S.order);

  lemma_mod_mul_distr_r (S.pow kInv (S.order - 2)) (pow2 256) S.order;
  lemmaToDomain (S.pow kInv (S.order - 2))


inline_for_extraction
val ecdsa_signature_step6: result: felem
  -> kFelem: felem
  -> z: felem
  -> r: felem
  -> da: felem
  -> Stack unit
    (requires fun h ->
      live h result /\ live h kFelem /\ live h z /\ live h r /\ live h da /\
      eq_or_disjoint r da /\
      as_nat h kFelem < S.order /\
      as_nat h z < S.order /\
      as_nat h r < S.order /\
      as_nat h da < S.order
    )
    (ensures fun h0 _ h1 ->
      modifies (loc result) h0 h1 /\
      as_nat h1 result = (as_nat h0 z + as_nat h0 r * as_nat h0 da) * S.pow (as_nat h0 kFelem) (S.order - 2) % S.order
    )

let ecdsa_signature_step6 result kFelem z r da =
  let open FStar.Tactics in
  let open FStar.Tactics.Canon in
  push_frame();
    let rda = create (size 4) (u64 0) in
    let zBuffer = create (size 4) (u64 0) in
    let kInv = create (size 4) (u64 0) in
  let h0 = ST.get() in
    qmul r da rda;
    fromDomainImpl z zBuffer;
    qadd rda zBuffer zBuffer;
    copy kInv kFelem;
    qinv kInv;
    qmul zBuffer kInv result;
  pop_frame();
      let br0 = as_nat h0 z + as_nat h0 r * as_nat h0 da in
      let br1 = S.pow (as_nat h0 kFelem) (S.order - 2) in

      lemmaFromDomain (as_nat h0 r * as_nat h0 da);
      lemma_power_step6 (as_nat h0 kFelem);

      lemmaFromDomain (fromDomain_ br0);
      lemmaToDomain br1;
      assert_norm ((S.modp_inv2_prime (pow2 256) S.order * pow2 256) % S.order = 1);

      lemma_mod_mul_distr_l (fromDomain_ br0 * S.modp_inv2_prime (pow2 256) S.order) (br1 * pow2 256 % S.order) S.order;
      lemma_mod_mul_distr_r (fromDomain_ br0 * S.modp_inv2_prime (pow2 256) S.order) (br1 * pow2 256) S.order;

      assert_by_tactic (fromDomain_ br0 * S.modp_inv2_prime (pow2 256) S.order * (br1 * pow2 256) == fromDomain_ br0 * S.modp_inv2_prime (pow2 256) S.order * br1 * pow2 256) canon;
      assert_by_tactic (fromDomain_ br0 * br1 * (S.modp_inv2_prime (pow2 256) S.order * pow2 256) == fromDomain_ br0 * S.modp_inv2_prime (pow2 256) S.order * br1 * pow2 256) canon;

      lemma_mod_mul_distr_r (fromDomain_ br0 * br1) (S.modp_inv2_prime (pow2 256) S.order * pow2 256) S.order;
      lemmaToDomain ((fromDomain_ br0 * br1) % S.order);
      lemmaFromDomain br0;

      lemma_mod_mul_distr_l (br0 * S.modp_inv2_prime (pow2 256) S.order) br1 S.order;
      lemma_mod_mul_distr_l (br0 * S.modp_inv2_prime (pow2 256) S.order * br1) (pow2 256) S.order;

      assert_by_tactic (br0 * S.modp_inv2_prime (pow2 256) S.order * br1 * pow2 256 = br0 * br1 * (S.modp_inv2_prime (pow2 256) S.order * pow2 256)) canon;
      lemma_mod_mul_distr_r (br0 * br1) (S.modp_inv2_prime (pow2 256) S.order * pow2 256) S.order;
      lemma_mod_mul_distr_r br0 br1 S.order

#push-options "--ifuel 1"

val ecdsa_signature_core: alg: S.hash_alg_ecdsa
  -> r: felem
  -> s: felem
  -> mLen: size_t {v mLen >= S.min_input_length alg}
  -> m: lbuffer uint8 mLen
  -> privKeyAsFelem: felem
  -> k: lbuffer uint8 (size 32) ->
  Stack uint64
  (requires fun h ->
    live h r /\ live h s /\ live h m /\ live h privKeyAsFelem /\ live h k /\
    disjoint privKeyAsFelem r /\
    disjoint privKeyAsFelem s /\
    disjoint k r /\
    disjoint r s /\
    as_nat h privKeyAsFelem < S.order /\
    as_nat h s == 0 /\
    nat_from_bytes_be (as_seq h k) < S.order
  )
  (ensures fun h0 flag h1 ->
    modifies (loc r |+| loc s) h0 h1 /\
    (
      assert_norm (pow2 32 < pow2 61);
      assert_norm (pow2 32 < pow2 125);
      let hashM = S.hash_ecdsa alg (v mLen) (as_seq h0 m) in
      let cutHashM = Lib.Sequence.sub hashM 0 32 in
      let z =  nat_from_bytes_be cutHashM % S.order in
      let (rxN, ryN, rzN), _ = S.montgomery_ladder_spec (as_seq h0 k) ((0,0,0), S.base_point) in
      let (xN, _, _) = S.norm_jacob_point (rxN, ryN, rzN) in

      let kFelem = nat_from_bytes_be (as_seq h0 k) in
      as_nat h1 r == xN % S.order /\
      as_nat h1 s == (z + (as_nat h1 r) * as_nat h0 privKeyAsFelem) * S.pow kFelem (S.order - 2) % S.order /\
      (
	if as_nat h1 r = 0 || as_nat h1 s = 0 then
	  uint_v flag == pow2 64 - 1
	else
	  uint_v flag == 0
      )
    )
  )


let ecdsa_signature_core alg r s mLen m privKeyAsFelem k =
  push_frame();
  let h0 = ST.get() in
  let hashAsFelem = create (size 4) (u64 0) in
  let tempBuffer = create (size 100) (u64 0) in
  let kAsFelem = create (size 4) (u64 0) in
  bn_from_bytes_be4 k kAsFelem;
  ecdsa_signature_step12 alg mLen m hashAsFelem;
  let h1 = ST.get() in
  lemma_core_0 kAsFelem h1;
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 k);
  let step5Flag = ecdsa_signature_step45 r k tempBuffer in
  assert_norm (pow2 32 < pow2 61);
  ecdsa_signature_step6 s kAsFelem hashAsFelem r privKeyAsFelem;
  let sIsZero = bn_is_zero_mask4 s in
  logor_lemma step5Flag sIsZero;
  pop_frame();
  logor step5Flag sIsZero

#pop-options

inline_for_extraction noextract
val ecdsa_signature: alg: S.hash_alg_ecdsa
  -> result: lbuffer uint8 (size 64)
  -> mLen: size_t {v mLen >= S.min_input_length alg}
  -> m: lbuffer uint8 mLen
  -> privKey: lbuffer uint8 (size 32)
  -> k: lbuffer uint8 (size 32) ->
  Stack bool
  (requires fun h ->
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < S.order /\
    nat_from_bytes_be (as_seq h k) < S.order
  )
  (ensures fun h0 flag h1 -> modifies (loc result) h0 h1 /\
    (let sgnt = S.ecdsa_signature_agile alg (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in
      (flag <==> Some? sgnt) /\ (flag ==> (as_seq h1 result == Some?.v sgnt))))


let ecdsa_signature alg result mLen m privKey k =
  push_frame();
  let h0 = ST.get() in
  assert_norm (pow2 32 < pow2 61);
  let privKeyAsFelem = create (size 4) (u64 0) in
  let r = create (size 4) (u64 0) in
  let s = create (size 4) (u64 0) in
  let resultR = sub result (size 0) (size 32) in
  let resultS = sub result (size 32) (size 32) in
  bn_from_bytes_be4 privKey privKeyAsFelem;

  let h1 = ST.get() in
  lemma_core_0 privKeyAsFelem h1;
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 privKey);
  let flag = ecdsa_signature_core alg r s mLen m privKeyAsFelem k in

  let h2 = ST.get() in

  bn_to_bytes_be4 r resultR;
  lemma_core_0 r h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 r);

  bn_to_bytes_be4 s resultS;
  let h3 = ST.get() in
  lemma_core_0 s h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 s);

  pop_frame();

  let open Hacl.Impl.P256.RawCmp in
  unsafe_bool_of_u64  flag
