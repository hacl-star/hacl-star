module Hacl.Hash.SHA3.Scalar

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
open Hacl.Impl.SHA3.Vec

module S = Spec.SHA3
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val shake128:
  output:buffer_t MUT uint8
  -> outputByteLen:size_t{v outputByteLen == length output}
  -> input:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 (output <: lbuffer uint8 outputByteLen) ==
       S.shake128 (v inputByteLen) (as_seq h0 (input <: lbuffer uint8 inputByteLen)) (v outputByteLen))
let shake128 output outputByteLen input inputByteLen =
  admit();
  keccak #Shake128 #M32 1344ul (* 256ul *) inputByteLen input (byte 0x1F) outputByteLen output

val shake256:
  output:buffer_t MUT uint8
  -> outputByteLen:size_t{v outputByteLen == length output}
  -> input:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 (output <: lbuffer uint8 outputByteLen) ==
       S.shake256 (v inputByteLen) (as_seq h0 (input <: lbuffer uint8 inputByteLen)) (v outputByteLen))
let shake256 output outputByteLen input inputByteLen =
  admit();
  keccak #Shake256 #M32 1088ul (* 512ul *) inputByteLen input (byte 0x1F) outputByteLen output

val sha3_224:
  output:lbuffer uint8 28ul
  -> input:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_224 (v inputByteLen) (as_seq h0 (input <: lbuffer uint8 inputByteLen)))
let sha3_224 output input inputByteLen =
  admit();
  keccak #SHA3_224 #M32 1152ul (* 448ul *) inputByteLen input (byte 0x06) 28ul output

val sha3_256:
  output:lbuffer uint8 32ul
  -> input:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_256 (v inputByteLen) (as_seq h0 (input <: lbuffer uint8 inputByteLen)))
let sha3_256 output input inputByteLen =
  admit();
  keccak #SHA3_256 #M32 1088ul (* 512ul *) inputByteLen input (byte 0x06) 32ul output

val sha3_384:
  output:lbuffer uint8 48ul
  -> input:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_384 (v inputByteLen) (as_seq h0 (input <: lbuffer uint8 inputByteLen)))
let sha3_384 output input inputByteLen =
  admit();
  keccak #SHA3_384 #M32 832ul (* 768ul *) inputByteLen input (byte 0x06) 48ul output

val sha3_512:
  output:lbuffer uint8 64ul
  -> input:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_512 (v inputByteLen) (as_seq h0 (input <: lbuffer uint8 inputByteLen)))
let sha3_512 output input inputByteLen =
  admit();
  keccak #SHA3_512 #M32 576ul (* 1024ul *) inputByteLen input (byte 0x06) 64ul output
