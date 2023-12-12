module Hacl.Hash.SHA3.Simd256

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.NTuple
open Lib.Buffer
open Lib.ByteBuffer
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
open Hacl.Impl.SHA3.Vec

module S = Spec.SHA3
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val shake128:
  output0:buffer_t MUT uint8
  -> output1:buffer_t MUT uint8
  -> output2:buffer_t MUT uint8
  -> output3:buffer_t MUT uint8
  -> outputByteLen:size_t{v outputByteLen == length output0 /\ 
                          v outputByteLen == length output1 /\
                          v outputByteLen == length output2 /\
                          v outputByteLen == length output3}
  -> input0:buffer_t MUT uint8
  -> input1:buffer_t MUT uint8
  -> input2:buffer_t MUT uint8
  -> input3:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input0 /\ 
                         v inputByteLen == length input1 /\
                         v inputByteLen == length input2 /\
                         v inputByteLen == length input3}
  -> Stack unit
     (requires fun h ->
       live4 h (input0 <: lbuffer uint8 inputByteLen)
               (input1 <: lbuffer uint8 inputByteLen)
               (input2 <: lbuffer uint8 inputByteLen)
               (input3 <: lbuffer uint8 inputByteLen) /\
       live4 h (output0 <: lbuffer uint8 outputByteLen)
               (output1 <: lbuffer uint8 outputByteLen)
               (output2 <: lbuffer uint8 outputByteLen)
               (output3 <: lbuffer uint8 outputByteLen) /\
       internally_disjoint4 (output0 <: lbuffer uint8 outputByteLen)
                            (output1 <: lbuffer uint8 outputByteLen)
                            (output2 <: lbuffer uint8 outputByteLen)
                            (output3 <: lbuffer uint8 outputByteLen))
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 (output0 <: lbuffer uint8 outputByteLen) ==
        S.shake128 (v inputByteLen) (as_seq h0 (input0 <: lbuffer uint8 inputByteLen)) (v outputByteLen) /\
       as_seq h1 (output1 <: lbuffer uint8 outputByteLen) ==
        S.shake128 (v inputByteLen) (as_seq h0 (input1 <: lbuffer uint8 inputByteLen)) (v outputByteLen) /\
       as_seq h1 (output2 <: lbuffer uint8 outputByteLen) ==
        S.shake128 (v inputByteLen) (as_seq h0 (input2 <: lbuffer uint8 inputByteLen)) (v outputByteLen) /\
       as_seq h1 (output3 <: lbuffer uint8 outputByteLen) ==
        S.shake128 (v inputByteLen) (as_seq h0 (input3 <: lbuffer uint8 inputByteLen)) (v outputByteLen))
let shake128 output0 output1 output2 output3 outputByteLen
      input0 input1 input2 input3 inputByteLen =
  admit();
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  keccak #Shake128 #M256 1344ul (* 256ul *) inputByteLen ib (byte 0x1F) outputByteLen rb

val shake256:
  output0:buffer_t MUT uint8
  -> output1:buffer_t MUT uint8
  -> output2:buffer_t MUT uint8
  -> output3:buffer_t MUT uint8
  -> outputByteLen:size_t{v outputByteLen == length output0 /\ 
                          v outputByteLen == length output1 /\
                          v outputByteLen == length output2 /\
                          v outputByteLen == length output3}
  -> input0:buffer_t MUT uint8
  -> input1:buffer_t MUT uint8
  -> input2:buffer_t MUT uint8
  -> input3:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input0 /\ 
                         v inputByteLen == length input1 /\
                         v inputByteLen == length input2 /\
                         v inputByteLen == length input3}
  -> Stack unit
     (requires fun h ->
       live4 h (input0 <: lbuffer uint8 inputByteLen)
               (input1 <: lbuffer uint8 inputByteLen)
               (input2 <: lbuffer uint8 inputByteLen)
               (input3 <: lbuffer uint8 inputByteLen) /\
       live4 h (output0 <: lbuffer uint8 outputByteLen)
               (output1 <: lbuffer uint8 outputByteLen)
               (output2 <: lbuffer uint8 outputByteLen)
               (output3 <: lbuffer uint8 outputByteLen) /\
       internally_disjoint4 (output0 <: lbuffer uint8 outputByteLen)
                            (output1 <: lbuffer uint8 outputByteLen)
                            (output2 <: lbuffer uint8 outputByteLen)
                            (output3 <: lbuffer uint8 outputByteLen))
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 (output0 <: lbuffer uint8 outputByteLen) ==
        S.shake256 (v inputByteLen) (as_seq h0 (input0 <: lbuffer uint8 inputByteLen)) (v outputByteLen) /\
       as_seq h1 (output1 <: lbuffer uint8 outputByteLen) ==
        S.shake256 (v inputByteLen) (as_seq h0 (input1 <: lbuffer uint8 inputByteLen)) (v outputByteLen) /\
       as_seq h1 (output2 <: lbuffer uint8 outputByteLen) ==
        S.shake256 (v inputByteLen) (as_seq h0 (input2 <: lbuffer uint8 inputByteLen)) (v outputByteLen) /\
       as_seq h1 (output3 <: lbuffer uint8 outputByteLen) ==
        S.shake256 (v inputByteLen) (as_seq h0 (input3 <: lbuffer uint8 inputByteLen)) (v outputByteLen))
let shake256 output0 output1 output2 output3 outputByteLen
      input0 input1 input2 input3 inputByteLen =
  admit();
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  keccak #Shake256 #M256 1088ul (* 512ul *) inputByteLen ib (byte 0x1F) outputByteLen rb

val sha3_224:
  output0:lbuffer uint8 28ul
  -> output1:lbuffer uint8 28ul
  -> output2:lbuffer uint8 28ul
  -> output3:lbuffer uint8 28ul
  -> input0:buffer_t MUT uint8
  -> input1:buffer_t MUT uint8
  -> input2:buffer_t MUT uint8
  -> input3:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input0 /\ 
                         v inputByteLen == length input1 /\
                         v inputByteLen == length input2 /\
                         v inputByteLen == length input3}
  -> Stack unit
     (requires fun h ->
       live4 h (input0 <: lbuffer uint8 inputByteLen)
               (input1 <: lbuffer uint8 inputByteLen)
               (input2 <: lbuffer uint8 inputByteLen)
               (input3 <: lbuffer uint8 inputByteLen) /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 == S.sha3_224 (v inputByteLen) (as_seq h0 (input0 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output1 == S.sha3_224 (v inputByteLen) (as_seq h0 (input1 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output2 == S.sha3_224 (v inputByteLen) (as_seq h0 (input2 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output3 == S.sha3_224 (v inputByteLen) (as_seq h0 (input3 <: lbuffer uint8 inputByteLen)))
let sha3_224 output0 output1 output2 output3
        input0 input1 input2 input3 inputByteLen =
  admit();
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  keccak #SHA3_224 #M256 1152ul (* 448ul *) inputByteLen ib (byte 0x06) 28ul rb

val sha3_256:
  output0:lbuffer uint8 32ul
  -> output1:lbuffer uint8 32ul
  -> output2:lbuffer uint8 32ul
  -> output3:lbuffer uint8 32ul
  -> input0:buffer_t MUT uint8
  -> input1:buffer_t MUT uint8
  -> input2:buffer_t MUT uint8
  -> input3:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input0 /\ 
                         v inputByteLen == length input1 /\
                         v inputByteLen == length input2 /\
                         v inputByteLen == length input3}
  -> Stack unit
     (requires fun h ->
       live4 h (input0 <: lbuffer uint8 inputByteLen)
               (input1 <: lbuffer uint8 inputByteLen)
               (input2 <: lbuffer uint8 inputByteLen)
               (input3 <: lbuffer uint8 inputByteLen) /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 == S.sha3_256 (v inputByteLen) (as_seq h0 (input0 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output1 == S.sha3_256 (v inputByteLen) (as_seq h0 (input1 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output2 == S.sha3_256 (v inputByteLen) (as_seq h0 (input2 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output3 == S.sha3_256 (v inputByteLen) (as_seq h0 (input3 <: lbuffer uint8 inputByteLen)))
let sha3_256 output0 output1 output2 output3
        input0 input1 input2 input3 inputByteLen =
  admit();
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  keccak #SHA3_256 #M256 1088ul (* 512ul *) inputByteLen ib (byte 0x06) 32ul rb

val sha3_384:
  output0:lbuffer uint8 48ul
  -> output1:lbuffer uint8 48ul
  -> output2:lbuffer uint8 48ul
  -> output3:lbuffer uint8 48ul
  -> input0:buffer_t MUT uint8
  -> input1:buffer_t MUT uint8
  -> input2:buffer_t MUT uint8
  -> input3:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input0 /\ 
                         v inputByteLen == length input1 /\
                         v inputByteLen == length input2 /\
                         v inputByteLen == length input3}
  -> Stack unit
     (requires fun h ->
       live4 h (input0 <: lbuffer uint8 inputByteLen)
               (input1 <: lbuffer uint8 inputByteLen)
               (input2 <: lbuffer uint8 inputByteLen)
               (input3 <: lbuffer uint8 inputByteLen) /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 == S.sha3_384 (v inputByteLen) (as_seq h0 (input0 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output1 == S.sha3_384 (v inputByteLen) (as_seq h0 (input1 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output2 == S.sha3_384 (v inputByteLen) (as_seq h0 (input2 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output3 == S.sha3_384 (v inputByteLen) (as_seq h0 (input3 <: lbuffer uint8 inputByteLen)))
let sha3_384 output0 output1 output2 output3
        input0 input1 input2 input3 inputByteLen =
  admit();
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  keccak #SHA3_384 #M256 832ul (* 768ul *) inputByteLen ib (byte 0x06) 48ul rb

val sha3_512:
  output0:lbuffer uint8 64ul
  -> output1:lbuffer uint8 64ul
  -> output2:lbuffer uint8 64ul
  -> output3:lbuffer uint8 64ul
  -> input0:buffer_t MUT uint8
  -> input1:buffer_t MUT uint8
  -> input2:buffer_t MUT uint8
  -> input3:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input0 /\ 
                         v inputByteLen == length input1 /\
                         v inputByteLen == length input2 /\
                         v inputByteLen == length input3}
  -> Stack unit
     (requires fun h ->
       live4 h (input0 <: lbuffer uint8 inputByteLen)
               (input1 <: lbuffer uint8 inputByteLen)
               (input2 <: lbuffer uint8 inputByteLen)
               (input3 <: lbuffer uint8 inputByteLen) /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 == S.sha3_512 (v inputByteLen) (as_seq h0 (input0 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output1 == S.sha3_512 (v inputByteLen) (as_seq h0 (input1 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output2 == S.sha3_512 (v inputByteLen) (as_seq h0 (input2 <: lbuffer uint8 inputByteLen)) /\
       as_seq h1 output3 == S.sha3_512 (v inputByteLen) (as_seq h0 (input3 <: lbuffer uint8 inputByteLen)))
let sha3_512 output0 output1 output2 output3
        input0 input1 input2 input3 inputByteLen =
  admit();
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  keccak #SHA3_512 #M256 576ul (* 1024ul *) inputByteLen ib (byte 0x06) 64ul rb
