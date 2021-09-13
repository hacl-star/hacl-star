module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.EC.LowLevel 
open Hacl.Impl.EC.Exponent
open Hacl.Impl.EC.Arithmetics

open Hacl.Impl.EC.LowLevel.RawCmp
open Hacl.EC.Lemmas

open Hacl.Spec.MontgomeryMultiplication

open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.Masking
open Hacl.Impl.EC.Setup
open Hacl.Impl.EC.Intro

open FStar.Math.Lemmas


open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Impl.EC.Core

open FStar.Mul

#set-options "--z3rlimit 200 --ifuel 0 --fuel 0"


val computeYFromX: #c: curve -> x: felem c -> result: felem c -> sign: uint64 -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ as_nat c h x < getPrime c /\ disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat c h1 result < getPrime c /\ (
    let prime = getPrime c in 
    let xD = fromDomain_ #c #DH (as_nat c h0 x) in 
    let sqRootWithoutSign = sq_root_spec #c #DH (((xD * xD * xD + aCoordinate #c * xD + bCoordinate #c) % prime)) in 
    if sqRootWithoutSign % pow2 1 = uint_v sign then
      as_nat c h1 result = sqRootWithoutSign 
    else
      as_nat c h1 result = (0 - sqRootWithoutSign) % prime))


let computeYFromX #c x result sign = 
  push_frame();
    let len = getCoordinateLenU64 c in 
    
    let aCoordinateBuffer = create len (u64 0) in 
    let bCoordinateBuffer = create len (u64 0) in 

  let h0 = ST.get() in 
    uploadA #c aCoordinateBuffer;
    uploadB #c bCoordinateBuffer;
    
    montgomery_multiplication_buffer_dh aCoordinateBuffer x aCoordinateBuffer;
    cube x result;
    felem_add result aCoordinateBuffer result;
    felem_add result bCoordinateBuffer result;

    uploadZeroImpl #c aCoordinateBuffer; 

  let h1 = ST.get() in 
  
    lemmaFromDomain #c #DH (as_nat c h1 aCoordinateBuffer);
    Hacl.Impl.EC.MontgomeryMultiplication.Lemmas.fromDomain_zero #c; 
    square_root result result;

  let h2 = ST.get() in 
  
    lemmaFromDomainToDomain #c #DH (as_nat c h2 result);
    fromDomain result result; 
    felem_sub aCoordinateBuffer result bCoordinateBuffer; 

  let h3 = ST.get() in 

    let word = index result (size 0) in 
    let bitToCheck = logand word (u64 1) in 
      logand_mask word (u64 1) 1;
    let flag = eq_mask bitToCheck sign in 
      eq_mask_lemma bitToCheck sign;

  let h4 = ST.get() in 

    cmovznz4 flag bCoordinateBuffer result result;
    assert(modifies (loc aCoordinateBuffer |+| loc bCoordinateBuffer |+| loc result) h0 h3);
    pop_frame();

  let len = v (getCoordinateLenU64 c) in 

  lemma_core_0 c result h4;
  Lib.ByteSequence.lemma_nat_from_to_intseq_le_preserves_value len (as_seq h4 result);
  Lib.ByteSequence.index_nat_to_intseq_le #U64 #SEC len (as_nat c h4 result) 0;


  let x_ = fromDomain_ #c #DH (as_nat c h0 x) in
  let prime = getPrime c in 

  calc (==) {
       ((((x_ * x_ * x_ % prime + Spec.ECC.Curves.aCoordinate #c % prime * x_ % prime) % prime) + Spec.ECC.Curves.bCoordinate #c) % prime);
    (==) {lemma_mod_add_distr (bCoordinate #c) (x_ * x_ * x_ % prime + ((Spec.ECC.Curves.aCoordinate #c % prime) * x_ % prime)) prime}
      ((x_ * x_ * x_ % prime + (Spec.ECC.Curves.aCoordinate #c % prime) * x_ % prime + Spec.ECC.Curves.bCoordinate #c) % prime);
    (==) {lemma_mod_add_distr ((Spec.ECC.Curves.aCoordinate #c % prime) * x_ % prime + Spec.ECC.Curves.bCoordinate #c) (x_ * x_ * x_) prime}
      ((x_ * x_ * x_ + (Spec.ECC.Curves.aCoordinate #c % prime) * x_ % prime + Spec.ECC.Curves.bCoordinate #c) % prime); 
    (==) {lemma_mod_mul_distr_l (aCoordinate #c) x_ prime}
      ((x_ * x_ * x_ + Spec.ECC.Curves.aCoordinate #c * x_ % prime + Spec.ECC.Curves.bCoordinate #c) % prime); 
    (==) {lemma_mod_add_distr (x_ * x_ * x_ + bCoordinate #c) (aCoordinate #c * x_) prime}
      ((x_ * x_ * x_ + Spec.ECC.Curves.aCoordinate #c * x_ + Spec.ECC.Curves.bCoordinate #c) % prime); }




let decompressionNotCompressedForm #c b result = 
  let h0 = ST.get() in 
  let compressionIdentifier = index b (size 0) in
  let correctIdentifier = eq_u8_nCT (u8 4) compressionIdentifier in 
  if correctIdentifier then 
    copy result (sub b (size 1) (size 2 *! getCoordinateLenU c));
  correctIdentifier


inline_for_extraction noextract
val lessThanPrime: #c: curve -> f: felem c -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 ->
    let prime = getPrime c in 
    modifies0 h0 h1 /\ r = (as_nat c h0 f < prime))

let lessThanPrime #c f = 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let tempBuffer = create c (u64 0) in 
    recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c));
    let carry = sub_bn_prime f tempBuffer in 
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

let decompressionCompressedForm #c b result = 
  push_frame();
    let h0 = ST.get() in 
      let len = getCoordinateLenU64 c in 
    let temp = create (size 2 *! len) (u64 0) in 
      let t0 = sub temp (size 0) len in 
      let t1 = sub temp len len in 
    let compressedIdentifier = index b (size 0) in 
    let flag = isIdentifierCorrect compressedIdentifier in 
    if flag then 
    begin

      let x = sub b (size 1) (getCoordinateLen c) in 
      copy (sub result (size 0) (getCoordinateLenU c)) x;
      toUint64ChangeEndian #c x t0;
	let h1 = ST.get() in 
      lemma_core_0 c t0 h1;

      let lessThanPrimeXCoordinate = lessThanPrime #c t0 in 
      (* changeEndianLemma #c (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 x)); *)
	Lib.ByteSequence.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 x);

      if not (lessThanPrimeXCoordinate) then 
	begin
	  pop_frame();
	  false
	end  
      else 
	begin 
	  toDomain #c t0 t0;
	  lemmaToDomain #c #DH (as_nat c h1 t0);
	    let h2 = ST.get() in 
      (* This is the function from Spec*)
	    (* assert(as_nat c h2 t0 =  (toDomain_ #c (Lib.ByteSequence.nat_from_intseq_le (changeEndian #c (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 x)))))); *)

	  let identifierBit = to_u64 (logand compressedIdentifier (u8 1)) in 
	  logand_mask compressedIdentifier (u8 1) 1;
	  computeYFromX #c t0 t1 identifierBit;
	  lemmaToDomainFromDomain #c #DH (Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x));

	    let h3 = ST.get() in 
	    assert(    
	      let xD = Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x) in 
	      let sqRootWithoutSign = sq_root_spec #c #DH (((xD * xD * xD + Spec.ECC.Curves.aCoordinate #P256 * xD + Spec.ECC.Curves.bCoordinate #P256) % prime256)) in 
	      if sqRootWithoutSign  % pow2 1 = uint_v identifierBit then
		 as_nat c h3 t1 = sqRootWithoutSign 
	      else
		as_nat c h3 t1 = (0 - sqRootWithoutSign) % prime256);
    
	  changeEndian #c t1;
	  toUint8 #c t1 (sub result (getCoordinateLenU c) (getCoordinateLenU c)); 
	   let h5 = ST.get() in 
     (*  This is the function from Spec *)
	   (* assert(as_seq h5 (gsub result (size 32) (size 32)) == Lib.ByteSequence.uints_to_bytes_be (changeEndian #c (as_seq h3 t1))); *)

	  lemma_core_0 c t1 h3;
	  
	  Lib.ByteSequence.lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h3 t1);
	  (* changeEndian_le_be #c (as_nat c h3 t1); *)
	  
	  assert(   
	      let xD = Lib.ByteSequence.nat_from_intseq_be (as_seq h0 x) in 
	      let sqRootWithoutSign = sq_root_spec #c #DH (((xD * xD * xD + Spec.ECC.Curves.aCoordinate #P256 * xD + Spec.ECC.Curves.bCoordinate #P256) % prime256)) in 
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


let compressionNotCompressedForm #c b result = 
  let lenCoordinate = getCoordinateLenU c in 
  let to = sub result (size 1) (size 2 *! lenCoordinate) in 
  copy to b;
  upd result (size 0) (u8 4)
 

let compressionCompressedForm #c b result = 
  let open Lib.ByteSequence in 
    let h0 = ST.get() in 
    
  let y = sub b (getCoordinateLenU c) (getCoordinateLenU c) in
    lemma_uint_to_bytes_be_preserves_value (Lib.Sequence.index (as_seq h0 y) 0);
    lemma_nat_from_to_intseq_be_preserves_value (getCoordinateLen c) (as_seq h0 y);

  
  let lastWordY = index y (getCoordinateLenU c -! 1ul) in 
  let lastBitY = logand lastWordY (u8 1) in 
    logand_mask lastWordY (u8 1) 1;
  let identifier = add lastBitY (u8 2) in 
  
  copy (sub result (size 1) (getCoordinateLenU c)) (sub b (size 0) (getCoordinateLenU c)) ;
  
  upd result (size 0) identifier;
    index_nat_to_intseq_be #U8 #SEC 32 (nat_from_bytes_be (as_seq h0 y)) 0;
    pow2_modulo_modulo_lemma_1 (nat_from_intseq_be (as_seq h0 y)) 1 8
