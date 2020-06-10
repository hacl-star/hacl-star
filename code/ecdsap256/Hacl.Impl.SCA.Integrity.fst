module Hacl.Impl.SCA.Integrity


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence


assume val integrity_specification: #a: Type0 -> len: size_nat ->  b: lseq a len -> uint8


assume val generateIntegrityValue: #a: Type0 -> len: size_t -> b: lbuffer a len -> 
  Stack uint8
    (requires fun h -> live h b)
    (ensures fun h0 r h1 -> modifies0 h0 h1 /\
      r == integrity_specification (uint_v len) (as_seq h0 b)
    )

assume val setIntegrityValue: 
  value: uint8
  -> index: size_t 
  -> bufLen: size_t {uint_v index < uint_v bufLen} 
  -> b: lbuffer uint8 bufLen -> 
  Stack unit
    (requires fun h -> live h b)
    (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      (
	let updatedValue = Lib.Sequence.index (as_seq h1 b) (uint_v index) in 
	updatedValue == value
      )
    )


assume val compareIntegrityValues: 
  bufLen: size_t ->
  b: lbuffer uint8 bufLen ->
  Stack uint64 
    (requires fun h -> live h b)
    (ensures fun h0 r h1 -> modifies0 h0 h1 /\
      (
	uint_v r == 0 <==> 
	(forall (i: nat). i < uint_v bufLen ==> 
	  uint_v (Lib.Sequence.index (as_seq h0 b) i) == uint_v (Lib.Sequence.index (as_seq h0 b) 0)
	)
      )
    )
