module Hacl.Impl.EC.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 0" 


let notCompressedForm (c: curve) = lbuffer uint8 (getCoordinateLenU c *! 2ul +! 1ul)

let compressedForm (c: curve) = lbuffer uint8 (getCoordinateLenU c +! 1ul)


inline_for_extraction
val decompressionNotCompressedForm: #c: curve -> b: notCompressedForm c -> result: lbuffer uint8 (getCoordinateLenU c *! 2ul) -> Stack bool 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
    let len = getCoordinateLen c in 
    
    let id = Lib.Sequence.index (as_seq h0 b) 0 in 
    let x = Lib.Sequence.sub (as_seq h0 b) 1 len in 
    let y = Lib.Sequence.sub (as_seq h0 b) (len + 1) len in 

    let xResult = Lib.Sequence.sub (as_seq h1 result) 0 len in 
    let yResult = Lib.Sequence.sub (as_seq h1 result) len len in 
    if uint_v id = 4 then 
       r == true /\ x == xResult /\ y == yResult
    else 
      r == false))


inline_for_extraction
val decompressionCompressedForm: #c: curve -> b: compressedForm c 
  -> result: lbuffer uint8 (getCoordinateLenU c *! 2ul) -> Stack bool 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
    let len = getCoordinateLen c in 
    let prime = getPrime c in 
    
    let id = Lib.Sequence.index (as_seq h0 b) 0 in 
    let xSequence = Lib.Sequence.sub (as_seq h0 b) 1 len in 
    let x =  Lib.ByteSequence.nat_from_bytes_be xSequence in 

    if uint_v id = 2 || uint_v id = 3 then
      if x < prime then 
	r == true /\ (
	let y = 
	  let sq = sq_root_spec #c #DH (((x * x * x + aCoordinate #c * x + bCoordinate #c) % prime)) in 
	  if (uint_v id) % 2 = sq % 2 then 
	    sq
	  else
	    (0 - sq) % prime in 
	as_seq h1 (gsub result (size 0) (getCoordinateLenU c)) == xSequence /\
	as_seq h1 (gsub result (getCoordinateLenU c) (getCoordinateLenU c)) == Lib.ByteSequence.nat_to_bytes_be len y)
      else 
	r == false
    else 
      r == false))
 

inline_for_extraction
val compressionNotCompressedForm: #c: curve -> b: lbuffer uint8 (getCoordinateLenU c *! 2ul) 
  -> result: notCompressedForm c -> Stack unit 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let len = getCoordinateLen c in
    
    let id = Lib.Sequence.index (as_seq h1 result) 0 in 
    let x = Lib.Sequence.sub (as_seq h0 b) 0 len in 
    let y = Lib.Sequence.sub (as_seq h0 b) len len in 
    
    let xResult = Lib.Sequence.sub (as_seq h1 result) 1 len in 
    let yResult = Lib.Sequence.sub (as_seq h1 result) (1 + len) len in 
    uint_v id == 4 /\ xResult == x /\ yResult == y))


inline_for_extraction
val compressionCompressedForm: #c: curve -> b: lbuffer uint8 (getCoordinateLenU c *! 2ul) -> result: compressedForm c -> 
  Stack unit 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let len = getCoordinateLen c in
    
    let identifier = Lib.Sequence.index (as_seq h1 result) 0 in 
    let x = Lib.Sequence.sub (as_seq h0 b) 0 len in 
    let y = Lib.Sequence.sub (as_seq h0 b) len len in 
    let xResult = Lib.Sequence.sub (as_seq h1 result) 1 len in 
    uint_v identifier == (Lib.ByteSequence.nat_from_intseq_be y % pow2 1) + 2 /\
    x == xResult))
