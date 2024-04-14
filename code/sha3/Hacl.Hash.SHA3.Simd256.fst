module Hacl.Hash.SHA3.Simd256

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.IntVector
open Lib.NTuple
open Lib.Buffer
open Lib.ByteBuffer
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
open Hacl.Impl.SHA3.Vec
open Hacl.Spec.SHA3.Equiv

module S = Spec.SHA3
module V = Hacl.Spec.SHA3.Vec
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let absorb_inner_256 rateInBytes b s = absorb_inner #M256 rateInBytes b s

inline_for_extraction noextract
let disjoint_in_out #len_in #len_out #a (b0 b1 b2 b3: lbuffer a len_in)
    (b4 b5 b6 b7: lbuffer a len_out) =
  disjoint b0 b4 /\ disjoint b0 b5 /\ disjoint b0 b6 /\ disjoint b0 b7 /\
  disjoint b1 b4 /\ disjoint b1 b5 /\ disjoint b1 b6 /\ disjoint b1 b7 /\
  disjoint b2 b4 /\ disjoint b2 b5 /\ disjoint b2 b6 /\ disjoint b2 b7 /\
  disjoint b3 b4 /\ disjoint b3 b5 /\ disjoint b3 b6 /\ disjoint b3 b7

inline_for_extraction noextract
let same_as x = y:size_t { x == y }

val shake128:
  g_outputByteLen:Ghost.erased size_t
  -> output0:lbuffer uint8 g_outputByteLen
  -> output1:lbuffer uint8 g_outputByteLen
  -> output2:lbuffer uint8 g_outputByteLen
  -> output3:lbuffer uint8 g_outputByteLen
  -> outputByteLen: same_as g_outputByteLen
  -> g_inputByteLen:Ghost.erased size_t
  -> input0:lbuffer uint8 g_inputByteLen
  -> input1:lbuffer uint8 g_inputByteLen
  -> input2:lbuffer uint8 g_inputByteLen
  -> input3:lbuffer uint8 g_inputByteLen
  -> inputByteLen: same_as g_inputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h input0 input1 input2 input3 /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3 /\
       disjoint_in_out input0 input1 input2 input3 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 ==
        S.shake128 (v inputByteLen) (as_seq h0 input0) (v outputByteLen) /\
       as_seq h1 output1 ==
        S.shake128 (v inputByteLen) (as_seq h0 input1) (v outputByteLen) /\
       as_seq h1 output2 ==
        S.shake128 (v inputByteLen) (as_seq h0 input2) (v outputByteLen) /\
       as_seq h1 output3 ==
        S.shake128 (v inputByteLen) (as_seq h0 input3) (v outputByteLen))
let shake128 _ output0 output1 output2 output3 outputByteLen
      _ input0 input1 input2 input3 inputByteLen =
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  assert (disjoint_multi_multi ib rb);
  loc_multi4 rb;
  keccak #M256 absorb_inner_256 1344ul (* 256ul *) inputByteLen ib (byte 0x1F) outputByteLen rb;
  let h1 = ST.get() in
  shake128_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 0;
  shake128_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 1;
  shake128_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 2;
  shake128_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 3;
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 output0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 output1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 output2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 output3)

val shake256:
  g_outputByteLen:Ghost.erased size_t
  -> output0:lbuffer uint8 g_outputByteLen
  -> output1:lbuffer uint8 g_outputByteLen
  -> output2:lbuffer uint8 g_outputByteLen
  -> output3:lbuffer uint8 g_outputByteLen
  -> outputByteLen: same_as g_outputByteLen
  -> g_inputByteLen:Ghost.erased size_t
  -> input0:lbuffer uint8 g_inputByteLen
  -> input1:lbuffer uint8 g_inputByteLen
  -> input2:lbuffer uint8 g_inputByteLen
  -> input3:lbuffer uint8 g_inputByteLen
  -> inputByteLen: same_as g_inputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h input0 input1 input2 input3 /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3 /\
       disjoint_in_out input0 input1 input2 input3 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 ==
        S.shake256 (v inputByteLen) (as_seq h0 input0) (v outputByteLen) /\
       as_seq h1 output1 ==
        S.shake256 (v inputByteLen) (as_seq h0 input1) (v outputByteLen) /\
       as_seq h1 output2 ==
        S.shake256 (v inputByteLen) (as_seq h0 input2) (v outputByteLen) /\
       as_seq h1 output3 ==
        S.shake256 (v inputByteLen) (as_seq h0 input3) (v outputByteLen))
let shake256 _ output0 output1 output2 output3 outputByteLen
      _ input0 input1 input2 input3 inputByteLen =
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  assert (disjoint_multi_multi ib rb);
  loc_multi4 rb;
  keccak #M256 absorb_inner_256 1088ul (* 512ul *) inputByteLen ib (byte 0x1F) outputByteLen rb;
  let h1 = ST.get() in
  shake256_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 0;
  shake256_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 1;
  shake256_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 2;
  shake256_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 3;
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 output0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 output1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 output2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 output3)

val sha3_224:
  output0:lbuffer uint8 28ul
  -> output1:lbuffer uint8 28ul
  -> output2:lbuffer uint8 28ul
  -> output3:lbuffer uint8 28ul
  -> g_inputByteLen:Ghost.erased size_t
  -> input0:lbuffer uint8 g_inputByteLen
  -> input1:lbuffer uint8 g_inputByteLen
  -> input2:lbuffer uint8 g_inputByteLen
  -> input3:lbuffer uint8 g_inputByteLen
  -> inputByteLen: same_as g_inputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h input0 input1 input2 input3 /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3 /\
       disjoint_in_out input0 input1 input2 input3 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 == S.sha3_224 (v inputByteLen) (as_seq h0 input0) /\
       as_seq h1 output1 == S.sha3_224 (v inputByteLen) (as_seq h0 input1) /\
       as_seq h1 output2 == S.sha3_224 (v inputByteLen) (as_seq h0 input2) /\
       as_seq h1 output3 == S.sha3_224 (v inputByteLen) (as_seq h0 input3))
let sha3_224 output0 output1 output2 output3
        _ input0 input1 input2 input3 inputByteLen =
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  assert (disjoint_multi_multi ib rb);
  loc_multi4 rb;
  keccak #M256 absorb_inner_256 1152ul (* 448ul *) inputByteLen ib (byte 0x06) 28ul rb;
  let h1 = ST.get() in
  sha3_224_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 0;
  sha3_224_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 1;
  sha3_224_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 2;
  sha3_224_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 3;
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 output0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 output1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 output2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 output3)

val sha3_256:
  output0:lbuffer uint8 32ul
  -> output1:lbuffer uint8 32ul
  -> output2:lbuffer uint8 32ul
  -> output3:lbuffer uint8 32ul
  -> g_inputByteLen:Ghost.erased size_t
  -> input0:lbuffer uint8 g_inputByteLen
  -> input1:lbuffer uint8 g_inputByteLen
  -> input2:lbuffer uint8 g_inputByteLen
  -> input3:lbuffer uint8 g_inputByteLen
  -> inputByteLen: same_as g_inputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h input0 input1 input2 input3 /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3 /\
       disjoint_in_out input0 input1 input2 input3 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 == S.sha3_256 (v inputByteLen) (as_seq h0 input0) /\
       as_seq h1 output1 == S.sha3_256 (v inputByteLen) (as_seq h0 input1) /\
       as_seq h1 output2 == S.sha3_256 (v inputByteLen) (as_seq h0 input2) /\
       as_seq h1 output3 == S.sha3_256 (v inputByteLen) (as_seq h0 input3))
let sha3_256 output0 output1 output2 output3
        _ input0 input1 input2 input3 inputByteLen =
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  assert (disjoint_multi_multi ib rb);
  loc_multi4 rb;
  keccak #M256 absorb_inner_256 1088ul (* 512ul *) inputByteLen ib (byte 0x06) 32ul rb;
  let h1 = ST.get() in
  sha3_256_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 0;
  sha3_256_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 1;
  sha3_256_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 2;
  sha3_256_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 3;
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 output0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 output1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 output2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 output3)

val sha3_384:
  output0:lbuffer uint8 48ul
  -> output1:lbuffer uint8 48ul
  -> output2:lbuffer uint8 48ul
  -> output3:lbuffer uint8 48ul
  -> g_inputByteLen:Ghost.erased size_t
  -> input0:lbuffer uint8 g_inputByteLen
  -> input1:lbuffer uint8 g_inputByteLen
  -> input2:lbuffer uint8 g_inputByteLen
  -> input3:lbuffer uint8 g_inputByteLen
  -> inputByteLen: same_as g_inputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h input0 input1 input2 input3 /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3 /\
       disjoint_in_out input0 input1 input2 input3 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 == S.sha3_384 (v inputByteLen) (as_seq h0 input0) /\
       as_seq h1 output1 == S.sha3_384 (v inputByteLen) (as_seq h0 input1) /\
       as_seq h1 output2 == S.sha3_384 (v inputByteLen) (as_seq h0 input2) /\
       as_seq h1 output3 == S.sha3_384 (v inputByteLen) (as_seq h0 input3))
let sha3_384 output0 output1 output2 output3
        _ input0 input1 input2 input3 inputByteLen =
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  assert (disjoint_multi_multi ib rb);
  loc_multi4 rb;
  keccak #M256 absorb_inner_256 832ul (* 768ul *) inputByteLen ib (byte 0x06) 48ul rb;
  let h1 = ST.get() in
  sha3_384_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 0;
  sha3_384_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 1;
  sha3_384_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 2;
  sha3_384_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 3;
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 output0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 output1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 output2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 output3)

val sha3_512:
  output0:lbuffer uint8 64ul
  -> output1:lbuffer uint8 64ul
  -> output2:lbuffer uint8 64ul
  -> output3:lbuffer uint8 64ul
  -> g_inputByteLen:Ghost.erased size_t
  -> input0:lbuffer uint8 g_inputByteLen
  -> input1:lbuffer uint8 g_inputByteLen
  -> input2:lbuffer uint8 g_inputByteLen
  -> input3:lbuffer uint8 g_inputByteLen
  -> inputByteLen: same_as g_inputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h input0 input1 input2 input3 /\
       live4 h output0 output1 output2 output3 /\
       internally_disjoint4 output0 output1 output2 output3 /\
       disjoint_in_out input0 input1 input2 input3 output0 output1 output2 output3)
     (ensures  fun h0 _ h1 ->
       modifies (loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       as_seq h1 output0 == S.sha3_512 (v inputByteLen) (as_seq h0 input0) /\
       as_seq h1 output1 == S.sha3_512 (v inputByteLen) (as_seq h0 input1) /\
       as_seq h1 output2 == S.sha3_512 (v inputByteLen) (as_seq h0 input2) /\
       as_seq h1 output3 == S.sha3_512 (v inputByteLen) (as_seq h0 input3))
let sha3_512 output0 output1 output2 output3
        _ input0 input1 input2 input3 inputByteLen =
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (output0,(output1,(output2,output3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  assert (disjoint_multi_multi ib rb);
  loc_multi4 rb;
  keccak #M256 absorb_inner_256 576ul (* 1024ul *) inputByteLen ib (byte 0x06) 64ul rb;
  let h1 = ST.get() in
  sha3_512_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 0;
  sha3_512_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 1;
  sha3_512_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 2;
  sha3_512_lemma_l M256 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 3;
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 output0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 output1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 output2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 output3)

[@@ Comment "Allocate quadruple state buffer (200-bytes for each)"]
inline_for_extraction
val state_malloc:
    r:rid
  -> ST.ST (s:buffer (vec_t U64 4) { length s = 25 })
  (requires (fun _ ->
    ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    live h1 s /\
    M.(modifies loc_none h0 h1) /\
    fresh_loc (loc_addr_of_buffer s) h0 h1 /\
    (M.loc_includes (M.loc_region_only true r) (loc_addr_of_buffer s)) /\
    freeable s))

let state_malloc r =
  malloc r (vec_zero U64 4) 25ul

[@@ Comment "Free quadruple state buffer"]
val state_free:
    s:buffer (vec_t U64 4) { length s = 25 }
  -> ST.ST unit
  (requires fun h0 ->
    freeable s /\ live h0 s)
  (ensures fun h0 _ h1 ->
    M.modifies (loc_addr_of_buffer s) h0 h1)

let state_free s =
  free s

[@@ Comment "Absorb number of blocks of 4 input buffers and write the output states

  This function is intended to receive a quadruple hash state and 4 input buffers.
  It prcoesses an inputs of multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block for each buffer are ignored.

  The argument `state` (IN/OUT) points to quadruple hash state,
  i.e., Lib_IntVector_Intrinsics_vec256[25]
  The arguments `input0/input1/input2/input3` (IN) point to `inputByteLen` bytes 
  of valid memory for each buffer, i.e., uint8_t[inputByteLen]"]
val shake128_absorb_nblocks:
  state:lbuffer_t MUT (vec_t U64 4) 25ul
  -> g_inputByteLen:Ghost.erased size_t
  -> input0:lbuffer uint8 g_inputByteLen
  -> input1:lbuffer uint8 g_inputByteLen
  -> input2:lbuffer uint8 g_inputByteLen
  -> input3:lbuffer uint8 g_inputByteLen
  -> inputByteLen: same_as g_inputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h input0 input1 input2 input3 /\
       live h state /\
       disjoint input0 state /\
       disjoint input1 state /\
       disjoint input2 state /\
       disjoint input3 state)
     (ensures  fun h0 _ h1 ->
       modifies (loc state) h0 h1 /\
       as_seq h1 state ==
          V.absorb_inner_nblocks #M256 168 (v inputByteLen) (as_seq_multi h0 (ntup4 (input0, (input1, (input2, input3))))) (as_seq h0 state))
let shake128_absorb_nblocks state _ input0 input1 input2 input3 inputByteLen =
  absorb_inner_nblocks #M256 absorb_inner_256 168ul inputByteLen (ntup4 (input0, (input1, (input2, input3)))) state

[@@ Comment "Absorb a final partial blocks of 4 input buffers and write the output states

  This function is intended to receive a quadruple hash state and 4 input buffers.
  It prcoesses a sequence of bytes at end of each input buffer that is less 
  than 168-bytes (SHAKE128 block size),
  any bytes of full blocks at start of input buffers are ignored.

  The argument `state` (IN/OUT) points to quadruple hash state,
  i.e., Lib_IntVector_Intrinsics_vec256[25]
  The arguments `input0/input1/input2/input3` (IN) point to `inputByteLen` bytes 
  of valid memory for each buffer, i.e., uint8_t[inputByteLen]
  
  Note: Full size of input buffers must be passed to `inputByteLen` including
  the number of full-block bytes at start of each input buffer that are ignored"]
val shake128_absorb_final:
  state:lbuffer_t MUT (vec_t U64 4) 25ul
  -> g_inputByteLen:Ghost.erased size_t
  -> input0:lbuffer uint8 g_inputByteLen
  -> input1:lbuffer uint8 g_inputByteLen
  -> input2:lbuffer uint8 g_inputByteLen
  -> input3:lbuffer uint8 g_inputByteLen
  -> inputByteLen: same_as g_inputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h input0 input1 input2 input3 /\
       live h state /\
       disjoint input0 state /\
       disjoint input1 state /\
       disjoint input2 state /\
       disjoint input3 state)
     (ensures  fun h0 _ h1 ->
       modifies (loc state) h0 h1 /\
       as_seq h1 state ==
         V.absorb_final #M256 (as_seq h0 state) 168 (v inputByteLen) (as_seq_multi h0 (ntup4 (input0, (input1, (input2, input3))))) (byte 0x1F))
let shake128_absorb_final state _ input0 input1 input2 input3 inputByteLen =
  absorb_final #M256 absorb_inner_256 168ul inputByteLen (ntup4 (input0, (input1, (input2, input3)))) (byte 0x1F) state

[@@ Comment "Squeeze a quadruple hash state to 4 output buffers

  This function is intended to receive a quadruple hash state and 4 output buffers.
  It produces 4 outputs, each is multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block for each buffer are ignored.

  The argument `state` (IN) points to quadruple hash state,
  i.e., Lib_IntVector_Intrinsics_vec256[25]
  The arguments `output0/output1/output2/output3` (OUT) point to `outputByteLen` bytes 
  of valid memory for each buffer, i.e., uint8_t[inputByteLen]"]
val shake128_squeeze_nblocks:
  state:lbuffer_t MUT (vec_t U64 4) 25ul
  -> g_outputByteLen:Ghost.erased size_t
  -> output0:lbuffer uint8 g_outputByteLen
  -> output1:lbuffer uint8 g_outputByteLen
  -> output2:lbuffer uint8 g_outputByteLen
  -> output3:lbuffer uint8 g_outputByteLen
  -> outputByteLen: same_as g_outputByteLen
  -> Stack unit
     (requires fun h ->
       live4 h output0 output1 output2 output3 /\
       live h state /\
       disjoint output0 output1 /\
       disjoint output0 output2 /\
       disjoint output0 output3 /\
       disjoint output1 output2 /\
       disjoint output1 output3 /\
       disjoint output2 output3 /\
       disjoint output0 state /\
       disjoint output1 state /\
       disjoint output2 state /\
       disjoint output3 state)
     (ensures  fun h0 _ h1 ->
       modifies (loc state |+| loc output0 |+| loc output1 |+| loc output2 |+| loc output3) h0 h1 /\
       (let s', b' = 
          V.squeeze_nblocks #M256 168 (v outputByteLen) (as_seq h0 state, as_seq_multi h0 (ntup4 #(lbuffer uint8 outputByteLen) #4 (output0, (output1, (output2, output3))))) in
          as_seq h1 state == s' /\
          as_seq_multi h1 (ntup4 #(lbuffer uint8 outputByteLen) #4 (output0, (output1, (output2, output3)))) == b'))
let shake128_squeeze_nblocks state _ output0 output1 output2 output3 outputByteLen =
  loc_multi4 #4 #outputByteLen (ntup4 (output0, (output1, (output2, output3))));
  squeeze_nblocks #M256 state 168ul outputByteLen (ntup4 (output0, (output1, (output2, output3))))
