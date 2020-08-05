module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Core
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MM.Exponent
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.P256.Arithmetics

open Hacl.Impl.P256.LowLevel .RawCmp

open Spec.P256.MontgomeryMultiplication

open Spec.P256.Definitions

open FStar.Math.Lemmas

open FStar.Mul

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

inline_for_extraction noextract
val uploadA: a: felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\ 
    as_nat h1 a == toDomain_ (Spec.P256.aCoordinateP256 % prime256) /\
    as_nat h1 a < prime256
  )

let uploadA a = 
  lemmaToDomain (Spec.P256.aCoordinateP256 % prime256);
  upd a (size 0) (u64 18446744073709551612);
  upd a (size 1) (u64 17179869183);
  upd a (size 2) (u64 0);
  upd a (size 3) (u64 18446744056529682436);
  assert_norm(18446744073709551612 + 17179869183 * pow2 64 + 18446744056529682436 * pow2 64 * pow2 64 * pow2 64 = (Spec.P256.aCoordinateP256 % prime256) * pow2 256 % prime256)

inline_for_extraction noextract
val uploadB: b: felem -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b < prime256 /\ 
    as_nat h1 b == toDomain_ (Spec.P256.bCoordinateP256)
  )

let uploadB b = 
  lemmaToDomain (Spec.P256.bCoordinateP256);
  upd b (size 0) (u64 15608596021259845087);
  upd b (size 1) (u64 12461466548982526096);
  upd b (size 2) (u64 16546823903870267094);
  upd b (size 3) (u64 15866188208926050356);
  assert_norm (15608596021259845087 + 12461466548982526096 * pow2 64 + 16546823903870267094 * pow2 64 * pow2 64 + 15866188208926050356 * pow2 64 * pow2 64 * pow2 64 == (Spec.P256.bCoordinateP256 * pow2 256 % prime256))


val computeYFromX: x: felem ->  result: felem -> sign: uint64 -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ as_nat h x < prime256 /\ disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result < prime256 /\
    (
      let xD = fromDomain_ (as_nat h0 x) in 
      let sqRootWithoutSign = sq_root_spec (((xD * xD * xD + Spec.P256.aCoordinateP256 * xD + Spec.P256.bCoordinateP256) % prime256)) in 
      
      if sqRootWithoutSign  % pow2 1 = uint_v sign then
	as_nat h1 result = sqRootWithoutSign 
      else
	as_nat h1 result = (0 - sqRootWithoutSign) % prime256
  )
)


let computeYFromX x result sign = 
  push_frame();
    let aCoordinateBuffer = create (size 4) (u64 0) in 
    let bCoordinateBuffer = create (size 4) (u64 0) in 

  let h0 = ST.get() in 
    uploadA aCoordinateBuffer;
    uploadB bCoordinateBuffer;
    
    montgomery_multiplication_buffer aCoordinateBuffer x aCoordinateBuffer;
  cube x result;
    p256_add result aCoordinateBuffer result;
    p256_add result bCoordinateBuffer result;

    uploadZeroImpl aCoordinateBuffer; 

  let h6 = ST.get() in 
  
    lemmaFromDomain (as_nat h6 aCoordinateBuffer);
    assert_norm (0 * Spec.P256.Lemmas.modp_inv2 (pow2 256) % prime256 == 0);
    square_root result result;

  let h7 = ST.get() in 
  
    lemmaFromDomainToDomain (as_nat h7 result);
    fromDomain result result; 

  let h8 = ST.get() in 
    p256_sub aCoordinateBuffer result bCoordinateBuffer; 

  let h9 = ST.get() in 

    let word = index result (size 0) in 
    let bitToCheck = logand word (u64 1) in 
      logand_mask word (u64 1) 1;

    let flag = eq_mask bitToCheck sign in 
      eq_mask_lemma bitToCheck sign;

    let h10 = ST.get() in 

    cmovznz4 flag bCoordinateBuffer result result;

    Spec.P256.Lemmas.lemma_core_0 result h10;
    Lib.ByteSequence.lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h10 result);
    Lib.ByteSequence.index_nat_to_intseq_le #U64 #SEC 4 (as_nat h10 result) 0;
    
    pow2_modulo_modulo_lemma_1 (as_nat h10 result) 1 64;

    assert(modifies (loc aCoordinateBuffer |+| loc bCoordinateBuffer |+| loc result) h0 h9);
    pop_frame();

  let x_ = fromDomain_ (as_nat h0 x) in

  calc (==) {
    ((((x_ * x_ * x_ % prime256 + ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256)) % prime256) + Spec.P256.bCoordinateP256) % prime256);
    (==) {lemma_mod_add_distr Spec.P256.bCoordinateP256 (x_ * x_ * x_ % prime256 + ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256)) prime256}
     ((x_ * x_ * x_ % prime256 + (Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256);
    (==) {lemma_mod_add_distr ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) (x_ * x_ * x_) prime256}
     ((x_ * x_ * x_ + (Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256); 
    (==) {lemma_mod_mul_distr_l Spec.P256.aCoordinateP256 x_ prime256}
    ((x_ * x_ * x_ + Spec.P256.aCoordinateP256 * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256); 
    (==) {lemma_mod_add_distr (x_ * x_ * x_ + Spec.P256.bCoordinateP256) (Spec.P256.aCoordinateP256 * x_) prime256}
    ((x_ * x_ * x_ + Spec.P256.aCoordinateP256 * x_ + Spec.P256.bCoordinateP256) % prime256); }


let decompressionNotCompressedForm b result = 
  let h0 = ST.get() in 
  let compressionIdentifier = index b (size 0) in
  let correctIdentifier = eq_u8_nCT (u8 4) compressionIdentifier in 
  if correctIdentifier then 
    copy result (sub b (size 1) (size 64));
  correctIdentifier

inline_for_extraction noextract
val lessThanPrime: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r = (as_nat h0 f < prime256))

let lessThanPrime f = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let carry = sub4_il f prime256_buffer tempBuffer in 
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



#push-options "--z3rlimit 300"

let decompressionCompressedForm b result = 
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
      assert (gsub b 1ul 32ul == x);
      toUint64ChangeEndian x t0;
	let h1 = ST.get() in 
      Spec.P256.Lemmas.lemma_core_0 t0 h1;

      let lessThanPrimeXCoordinate = lessThanPrime t0 in 
	Spec.ECDSA.changeEndianLemma (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 x));
	Lib.ByteSequence.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 x);

      if not (lessThanPrimeXCoordinate) then 
	begin
	  pop_frame();
	  false
	end  
      else 
	begin 
	  toDomain t0 t0;
	  lemmaToDomain (as_nat h1 t0);
	    let h2 = ST.get() in 
	    assert(as_nat h2 t0 =  (toDomain_ (Lib.ByteSequence.nat_from_intseq_le (Spec.ECDSA.changeEndian (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 x))))));

	  let identifierBit = to_u64 (logand compressedIdentifier (u8 1)) in 
	  logand_mask compressedIdentifier (u8 1) 1;
	  computeYFromX t0 t1 identifierBit;
	  lemmaToDomainAndBackIsTheSame (Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x));

	    let h3 = ST.get() in 
	    assert(    
	      let xD = Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x) in 
	      let sqRootWithoutSign = sq_root_spec (((xD * xD * xD + Spec.P256.aCoordinateP256 * xD + Spec.P256.bCoordinateP256) % prime256)) in 
	      if sqRootWithoutSign  % pow2 1 = uint_v identifierBit then
		 as_nat h3 t1 = sqRootWithoutSign 
	      else
		as_nat h3 t1 = (0 - sqRootWithoutSign) % prime256);
    
	  changeEndian t1;
	  toUint8 t1 (sub result (size 32) (size 32)); 
	   let h5 = ST.get() in 
	   assert(as_seq h5 (gsub result (size 32) (size 32)) == Lib.ByteSequence.uints_to_bytes_be (Spec.ECDSA.changeEndian (as_seq h3 t1)));

	  Spec.P256.Lemmas.lemma_core_0 t1 h3;
	  
	  Lib.ByteSequence.lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h3 t1);
	  Spec.ECDSA.changeEndian_le_be (as_nat h3 t1);
	  
	  assert(   
	      let xD = Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x) in 
	      let sqRootWithoutSign = sq_root_spec (((xD * xD * xD + Spec.P256.aCoordinateP256 * xD + Spec.P256.bCoordinateP256) % prime256)) in 
	      let to = as_seq h5 (gsub result (size 32) (size 32)) in 
	      if sqRootWithoutSign  % pow2 1 = uint_v identifierBit then
		 to == Lib.ByteSequence.nat_to_bytes_be 32 sqRootWithoutSign 
	      else
		to == Lib.ByteSequence.nat_to_bytes_be 32 ((0 - sqRootWithoutSign) % prime256)); 


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


let compressionNotCompressedForm b result = 
  let to = sub result (size 1) (size 64) in 
  copy to b;
  upd result (size 0) (u8 4)
 

let compressionCompressedForm b result = 
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
