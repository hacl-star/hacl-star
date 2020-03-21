module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256
open Hacl.Impl.LowLevel
open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256.MM.Exponent
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.P256.Arithmetics

open Spec.P256.MontgomeryMultiplication

open Spec.P256.Definitions

open FStar.Math.Lemmas

open FStar.Mul

#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"

val eq_u8_nCT: a:uint8 -> b:uint8 -> (r:bool{r == (uint_v a = uint_v b)})

let eq_u8_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

[@ CInline]
val copy_conditional_u8: out: lbuffer uint8 (size 64) -> x: lbuffer uint8 (size 64) -> mask: uint8{uint_v mask = 0 \/ uint_v mask = pow2 8 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1) 

let copy_conditional_u8 out x mask = 
  admit();
  [@inline_let]
  let inv h1 (i: nat {i <= 64}) = True in
  Lib.Loops.for 0ul 64ul inv 
    (fun i -> 
      let out_i = index out i in 
      let x_i = index x i in 
      let r_i = logxor out_i (logand mask (logxor out_i x_i)) in 
      upd out i r_i
    )
      

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

val uploadB: b: felem -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b < prime256 /\ 
    as_nat h1 b == toDomain_ (Spec.P256.bCoordinateP256))

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
    (
      let xD = fromDomain_ (as_nat h0 x) in 
      if uint_v sign = 0 then 
	as_nat h1 result = toDomain_ (sq_root_spec ((0 - (xD * xD * xD + Spec.P256.aCoordinateP256 * xD + Spec.P256.bCoordinateP256)) % prime256)) else
	as_nat h1 result = toDomain_ (sq_root_spec ((xD * xD * xD + Spec.P256.aCoordinateP256 * xD + Spec.P256.bCoordinateP256) % prime256)))
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
  p256_sub aCoordinateBuffer result bCoordinateBuffer;
    cmovznz4 sign bCoordinateBuffer result result;
    square_root result result;

  let h9 = ST.get() in 
    assert(modifies (loc aCoordinateBuffer |+| loc bCoordinateBuffer |+| loc result) h0 h9);
    lemmaFromDomainToDomain (as_nat h9 result);
    pop_frame();

  let x_ = fromDomain_ (as_nat h0 x) in

  calc (==) {
    toDomain_ ((((x_ * x_ * x_ % prime256 + ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256)) % prime256) + Spec.P256.bCoordinateP256) % prime256);
    (==) {lemma_mod_add_distr Spec.P256.bCoordinateP256 (x_ * x_ * x_ % prime256 + ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256)) prime256}
    toDomain_ ((x_ * x_ * x_ % prime256 + (Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256);
    (==) {lemma_mod_add_distr ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) (x_ * x_ * x_) prime256}
    toDomain_ ((x_ * x_ * x_ + (Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256); 
    (==) {lemma_mod_mul_distr_l Spec.P256.aCoordinateP256 x_ prime256}
    toDomain_ ((x_ * x_ * x_ + Spec.P256.aCoordinateP256 * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256); 
    (==) {lemma_mod_add_distr (x_ * x_ * x_ + Spec.P256.bCoordinateP256) (Spec.P256.aCoordinateP256 * x_) prime256}
    toDomain_ ((x_ * x_ * x_ + Spec.P256.aCoordinateP256 * x_ + Spec.P256.bCoordinateP256) % prime256); };

  lemma_mod_sub_distr 0 (x_ * x_ * x_ + Spec.P256.aCoordinateP256 * x_ + Spec.P256.bCoordinateP256) prime256
    
    


let decompressionNotCompressed b result = 
  let compressionIdentifier = index b (size 0) in
  let correctIdentifier = eq_u8_nCT (u8 4) compressionIdentifier in 
  if correctIdentifier then 
    copy (sub b (size 1) (size 64)) result;
  admit();  
  correctIdentifier


let decompressionNotCompressed2 b result = 
  let compressionIdentifier = index b (size 0) in 
  let correctIdentifier = eq_mask (u8 4) compressionIdentifier in 
    eq_mask_lemma (u8 4) compressionIdentifier;
  copy_conditional_u8 result (sub b (size 1) (size 64)) correctIdentifier;
  correctIdentifier

(* This code is not side channel resistant *)
(* inline_for_extraction noextract *)
val eq_u64_nCT: a:uint64 -> b:uint64 -> (r:bool{r == (uint_v a = uint_v b)})

let eq_u64_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)


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
    

val decompressionCompressed: b: compressedForm -> result: lbuffer uint8 (size 64) -> Stack bool 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1)


let decompressionCompressed b result = 
  push_frame();
    let temp = create (size 4) (u64 0) in 
  
  let compressedIdentifier = index b (size 0) in 
  let correctIdentifier2 = eq_u8_nCT (u8 2) compressedIdentifier in 
  let correctIdentifier3 = eq_u8_nCT (u8 3) compressedIdentifier in 
  
  if correctIdentifier2 || correctIdentifier3 then 
    begin
      let x = sub b (size 1) (size 32) in 
      copy x (sub result (size 0) (size 32));
(*till here I am BIG-ENDIAN *)
      toUint64ChangeEndian x temp;
      let lessThanPrimeXCoordinate = lessThanPrime temp in 
      if not (lessThanPrimeXCoordinate) then 
	begin
	  admit();
	  pop_frame();
	  false
	end  
      else 
	begin
	  toDomain temp temp;
	  computeYFromX temp (sub result (size 32) (size 32)) correctIdentifier2;
	  fromDomain temp temp;
	  toUint8 temp (sub result (size 32) (size 32));
	  true
	end
    end
  else 
    begin
      admit();
      pop_frame();
      false
    end
