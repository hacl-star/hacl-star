module Hacl.Impl.P256.Compression

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Math.Lemmas

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Impl.P256.Finv
open Hacl.Impl.P256.RawCmp
open Hacl.Impl.P256.Constants

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

val computeYFromX: x: felem ->  result: felem -> sign: uint64 -> Stack unit
  (requires fun h -> live h x /\ live h result /\ as_nat h x < S.prime /\ disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result < S.prime /\
    (
      let xD = SM.fromDomain_ (as_nat h0 x) in
      let sqRootWithoutSign = S.fsqrt (((xD * xD * xD + Spec.P256.a_coeff * xD + Spec.P256.b_coeff) % S.prime)) in

      if sqRootWithoutSign  % pow2 1 = uint_v sign then
	as_nat h1 result = sqRootWithoutSign
      else
	as_nat h1 result = (0 - sqRootWithoutSign) % S.prime
  )
)


let computeYFromX x result sign =
  push_frame();
    let aCoordinateBuffer = create (size 4) (u64 0) in
    let bCoordinateBuffer = create (size 4) (u64 0) in

  let h0 = ST.get() in
    make_a_coeff aCoordinateBuffer;
    make_b_coeff bCoordinateBuffer;

    fmul aCoordinateBuffer x aCoordinateBuffer;
  fcube x result;
    fadd result aCoordinateBuffer result;
    fadd result bCoordinateBuffer result;

    bn_set_zero4 aCoordinateBuffer;

  let h6 = ST.get() in

    SM.lemmaFromDomain (as_nat h6 aCoordinateBuffer);
    assert_norm (0 * Spec.P256.modp_inv2_prime (pow2 256) S.prime % S.prime == 0);
    fsqrt result result;

  let h7 = ST.get() in

    SM.lemmaFromDomainToDomain (as_nat h7 result);
    fromDomain result result;

  let h8 = ST.get() in
    fsub aCoordinateBuffer result bCoordinateBuffer;

  let h9 = ST.get() in

    let word = index result (size 0) in
    let bitToCheck = logand word (u64 1) in
      logand_mask word (u64 1) 1;

    let flag = eq_mask bitToCheck sign in
      eq_mask_lemma bitToCheck sign;

    let h10 = ST.get() in

    bn_cmovznz4 flag bCoordinateBuffer result result;

    lemma_core_0 result h10;
    Lib.ByteSequence.lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h10 result);
    Lib.ByteSequence.index_nat_to_intseq_le #U64 #SEC 4 (as_nat h10 result) 0;

    pow2_modulo_modulo_lemma_1 (as_nat h10 result) 1 64;

    assert(modifies (loc aCoordinateBuffer |+| loc bCoordinateBuffer |+| loc result) h0 h9);
    pop_frame();

  let x_ = SM.fromDomain_ (as_nat h0 x) in

  calc (==) {
    ((((x_ * x_ * x_ % S.prime + ((Spec.P256.a_coeff % S.prime) * x_ % S.prime)) % S.prime) + Spec.P256.b_coeff) % S.prime);
    (==) {lemma_mod_add_distr Spec.P256.b_coeff (x_ * x_ * x_ % S.prime + ((Spec.P256.a_coeff % S.prime) * x_ % S.prime)) S.prime}
     ((x_ * x_ * x_ % S.prime + (Spec.P256.a_coeff % S.prime) * x_ % S.prime + Spec.P256.b_coeff) % S.prime);
    (==) {lemma_mod_add_distr ((Spec.P256.a_coeff % S.prime) * x_ % S.prime + Spec.P256.b_coeff) (x_ * x_ * x_) S.prime}
     ((x_ * x_ * x_ + (Spec.P256.a_coeff % S.prime) * x_ % S.prime + Spec.P256.b_coeff) % S.prime);
    (==) {lemma_mod_mul_distr_l Spec.P256.a_coeff x_ S.prime}
    ((x_ * x_ * x_ + Spec.P256.a_coeff * x_ % S.prime + Spec.P256.b_coeff) % S.prime);
    (==) {lemma_mod_add_distr (x_ * x_ * x_ + Spec.P256.b_coeff) (Spec.P256.a_coeff * x_) S.prime}
    ((x_ * x_ * x_ + Spec.P256.a_coeff * x_ + Spec.P256.b_coeff) % S.prime); }


let uncompressed_to_raw b result =
  let h0 = ST.get() in
  let compressionIdentifier = index b (size 0) in
  let correctIdentifier = eq_u8_nCT (u8 4) compressionIdentifier in
  if correctIdentifier then
    copy result (sub b (size 1) (size 64));
  correctIdentifier

inline_for_extraction noextract
val lessThanPrime: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r = (as_nat h0 f < S.prime))

let lessThanPrime f =
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in
    recall_contents prime_buffer (Lib.Sequence.of_list p256_prime_list);
    let carry = bn_sub4_il f prime_buffer tempBuffer in
    let less = eq_u64_nCT carry (u64 1) in
  pop_frame();
    less

inline_for_extraction noextract
val isIdentifierCorrect: v: uint8 -> Tot (r: bool {r <==> uint_v v = 2 || uint_v v = 3})

let isIdentifierCorrect compressedIdentifier =
  let open Lib.RawIntTypes in
  let correctIdentifier2 = eq_mask (u8 2) compressedIdentifier in
    eq_mask_lemma (u8 2) compressedIdentifier;
  let correctIdentifier3 = eq_mask (u8 3) compressedIdentifier in
    eq_mask_lemma (u8 3) compressedIdentifier;
  let isIdentifierCorrect =  logor correctIdentifier2 correctIdentifier3 in
    logor_lemma correctIdentifier2 correctIdentifier3;
  u8_to_UInt8 isIdentifierCorrect = 255uy



#push-options "--z3rlimit 500"

let compressed_to_raw b result =
  push_frame();
    let h0 = ST.get() in
    let temp = create (size 8) (u64 0) in
      let t0 = sub temp (size 0) (size 4) in
      let t1 = sub temp (size 4) (size 4) in
    let compressedIdentifier = index b (size 0) in
    let flag = isIdentifierCorrect compressedIdentifier in
    if flag then
    begin

      let x = sub b (size 1) (size 32) in
      copy (sub result (size 0) (size 32)) x;
      bn_from_bytes_be4 x t0;
	let h1 = ST.get() in
      lemma_core_0 t0 h1;

      let lessThanPrimeXCoordinate = lessThanPrime t0 in
	Lib.ByteSequence.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 x);

      if not (lessThanPrimeXCoordinate) then
	begin
	  pop_frame();
	  false
	end
      else
	begin
	  toDomain t0 t0;
	  SM.lemmaToDomain (as_nat h1 t0);
	    let h2 = ST.get() in

	  let identifierBit = to_u64 (logand compressedIdentifier (u8 1)) in
	  logand_mask compressedIdentifier (u8 1) 1;
	  computeYFromX t0 t1 identifierBit;
	  SM.lemmaToDomainAndBackIsTheSame (Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x));

	    let h3 = ST.get() in
	    assert(
	      let xD = Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x) in
	      let sqRootWithoutSign = S.fsqrt (((xD * xD * xD + Spec.P256.a_coeff * xD + Spec.P256.b_coeff) % S.prime)) in
	      if sqRootWithoutSign  % pow2 1 = uint_v identifierBit then
		 as_nat h3 t1 = sqRootWithoutSign
	      else
		as_nat h3 t1 = (0 - sqRootWithoutSign) % S.prime);

	  bn_to_bytes_be4 t1 (sub result (size 32) (size 32));
	   let h5 = ST.get() in

	  lemma_core_0 t1 h3;

	  Lib.ByteSequence.lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h3 t1);

	  assert(
	      let xD = Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x) in
	      let sqRootWithoutSign = S.fsqrt (((xD * xD * xD + Spec.P256.a_coeff * xD + Spec.P256.b_coeff) % S.prime)) in
	      let to = as_seq h5 (gsub result (size 32) (size 32)) in
	      if sqRootWithoutSign  % pow2 1 = uint_v identifierBit then
		 to == Lib.ByteSequence.nat_to_bytes_be 32 sqRootWithoutSign
	      else
		to == Lib.ByteSequence.nat_to_bytes_be 32 ((0 - sqRootWithoutSign) % S.prime));


	  pop_frame();
	  true
	end
    end
  else
    begin
      pop_frame();
      false
    end

#pop-options


let raw_to_uncompressed b result =
  let to = sub result (size 1) (size 64) in
  copy to b;
  upd result (size 0) (u8 4)


let raw_to_compressed b result =
  let open Lib.ByteSequence in
    let h0 = ST.get() in
  let y = sub b (size 32) (size 32) in
    lemma_uint_to_bytes_be_preserves_value (Lib.Sequence.index (as_seq h0 y) 0);
    lemma_nat_from_to_intseq_be_preserves_value 32 (as_seq h0 y);

  let lastWordY = index y (size 31) in
  let lastBitY = logand lastWordY (u8 1) in
    logand_mask lastWordY (u8 1) 1;
  let identifier = add lastBitY (u8 2) in
  copy (sub result (size 1) (size 32)) (sub b (size 0) (size 32)) ;
  upd result (size 0) identifier;
    index_nat_to_intseq_be #U8 #SEC 32 (nat_from_bytes_be (as_seq h0 y)) 0;
    pow2_modulo_modulo_lemma_1 (nat_from_intseq_be (as_seq h0 y)) 1 8
