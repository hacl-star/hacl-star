module Hacl.Impl.P256.PointAdd8

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Lib.Buffer

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointAdd
open FStar.Mul

open Hacl.Impl.P256.Core
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.LowLevel

friend Hacl.Impl.P256.Core


#set-options "--z3rlimit 150 --ifuel 0 --fuel 0" 

inline_for_extraction noextract
val _point_add8: p: point -> q: point -> result: point -> tempBuffer: lbuffer uint64 (size 88) -> 
  Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ live h tempBuffer /\
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\ 
    as_nat h (gsub p (size 8) (size 4)) < prime /\
    as_nat h (gsub q (size 0) (size 4)) < prime /\ 
    as_nat h (gsub q (size 4) (size 4)) < prime /\  
    as_nat h (gsub q (size 8) (size 4)) < prime ) 
   (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc result |+| loc tempBuffer) h0 h1 /\
     as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
     as_nat h1 (gsub result (size 4) (size 4)) < prime /\  
     as_nat h1 (gsub result (size 8) (size 4)) < prime /\ (
     let pxD, pyD, pzD = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in 
     let qxD, qyD, qzD = as_nat h0 (gsub q (size 0) (size 4)), as_nat h0 (gsub q (size 4) (size 4)), as_nat h0 (gsub q (size 8) (size 4)) in 
     Spec.P256._norm (Spec.P256._point_add (pxD, pyD, pzD) (qxD, qyD, qzD)) =  Spec.P256.point_prime_to_coordinates (as_seq h1 result)))


let _point_add8 p q result tempBuffer = 
  pointToDomain p p;
  pointToDomain q q;
  point_add p q result tempBuffer;
  norm result result tempBuffer

inline_for_extraction noextract
val toForm: i: lbuffer uint8 (size 32) -> o: felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ Lib.ByteSequence.nat_from_bytes_be (as_seq h i) < prime256)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\ 
    as_nat h1 o == Lib.ByteSequence.nat_from_bytes_be (as_seq h0 i) /\
    as_nat h1 o < prime)

let toForm i o = 
  let open Lib.ByteSequence in 
    let h0 = ST.get() in 
  toUint64ChangeEndian i o;
    let h1 = ST.get() in 
  lemma_core_0 o h1;
  Spec.ECDSA.changeEndianLemma (uints_from_bytes_be (as_seq h0 i));
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 i)

inline_for_extraction noextract
val toFormPoint: p: lbuffer uint8 (size 64) -> o: point -> Stack unit 
  (requires fun h -> live h p /\ live h o /\ disjoint p o /\ (
    let pX = gsub p (size 0) (size 32) in 
    let pY = gsub p (size 32) (size 32) in 
    Lib.ByteSequence.nat_from_bytes_be (as_seq h pX) < prime256 /\
    Lib.ByteSequence.nat_from_bytes_be (as_seq h pY) < prime256))
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ (
    let pX, pY = gsub p (size 0) (size 32), gsub p (size 32) (size 32) in
    let rX, rY, rZ = gsub o (size 0) (size 4),  gsub o (size 4) (size 4), gsub o (size 8) (size 4) in 

    as_nat h1 rX == Lib.ByteSequence.nat_from_bytes_be (as_seq h0 pX) /\
    as_nat h1 rY == Lib.ByteSequence.nat_from_bytes_be (as_seq h0 pY) /\

    (as_nat h1 rX, as_nat h1 rY, as_nat h1 rZ) == 
      Spec.P256.toJacobianCoordinates (Lib.ByteSequence.nat_from_bytes_be (as_seq h0 pX), Lib.ByteSequence.nat_from_bytes_be (as_seq h0 pY)) /\
    as_nat h1 rX < prime /\ as_nat h1 rY < prime /\ as_nat h1 rZ == 1))

let toFormPoint i o = 
  let pU64X = sub o (size 0) (size 4) in
  let pU64Y = sub o (size 4) (size 4) in
  let pX = sub i (size 0) (size 32) in
  let pY = sub i (size 32) (size 32) in

  toForm pX pU64X;
  toForm pY pU64Y;
  Hacl.Impl.P256.Signature.Common.bufferToJacUpdate o



inline_for_extraction noextract
val fromForm: i: felem -> o: lbuffer uint8 (size 32) -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ as_nat h i < prime256)
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\  
    as_seq h1 o == Lib.ByteSequence.nat_to_bytes_be 32 (as_nat h0 i))


let fromForm i o = 
  let open Lib.ByteSequence in 
  let h0 = ST.get() in
  changeEndian i;
    let h1 = ST.get() in 
  toUint8 i o;
  lemma_core_0 i h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 i);
  Spec.ECDSA.changeEndian_le_be (as_nat h0 i)


inline_for_extraction noextract
val fromFormPoint: i: point -> o: lbuffer uint8 (size 64) -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ (
    let iX = gsub i (size 0) (size 4) in 
    let iY = gsub i (size 4) (size 4) in 
    as_nat h iX < prime256 /\ as_nat h iY < prime256))
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\ (
    let iX = gsub i (size 0) (size 4) in 
    let iY = gsub i (size 4) (size 4) in 

    let oX = gsub o (size 0) (size 32) in 
    let oY = gsub o (size 32) (size 32) in 

    as_seq h1 oX == Lib.ByteSequence.nat_to_bytes_be 32 (as_nat h0 iX) /\ 
    as_seq h1 oY == Lib.ByteSequence.nat_to_bytes_be 32 (as_nat h0 iY)))

let fromFormPoint i o = 
  let iX = sub i (size 0) (size 4) in 
  let iY = sub i (size 4) (size 4) in 

  let oX = sub o (size 0) (size 32) in 
  let oY = sub o (size 32) (size 32) in 

  fromForm iX oX;
  fromForm iY oY


let point_add8 result p q = 
  push_frame();
    let tempBuffer = create (size 124) (u64 0) in 
  
    let pU64 = sub tempBuffer (size 0) (size 12) in 
    let qU64 = sub tempBuffer (size 12) (size 12) in 
    let resultU64 = sub tempBuffer (size 24) (size 12) in 
    let tB88 = sub tempBuffer (size 36) (size 88) in 

    toFormPoint p pU64; 
    toFormPoint q qU64;
    _point_add8 pU64 qU64 resultU64 tB88;
    fromFormPoint resultU64 result;

  pop_frame()
