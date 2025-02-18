module Hacl.Hash.SHA3.Scalar

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.IntVector
open Lib.Buffer
open Lib.ByteBuffer
open Lib.NTuple
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
open Hacl.Impl.SHA3.Vec
open Hacl.Spec.SHA3.Equiv

module S = Spec.SHA3
module V = Hacl.Spec.SHA3.Vec
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let absorb_inner_32 rateInBytes b s = absorb_inner #M32 rateInBytes b s

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
  let ib = ntup1 input in
  let rb = ntup1 output in
  let h0 = ST.get () in
  keccak #M32 absorb_inner_32 1344ul (* 256ul *) inputByteLen ib (byte 0x1F) outputByteLen rb;
  shake128_lemma_l M32 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 0

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
  let ib = ntup1 input in
  let rb = ntup1 output in
  let h0 = ST.get () in
  keccak #M32 absorb_inner_32 1088ul (* 512ul *) inputByteLen ib (byte 0x1F) outputByteLen rb;
  shake256_lemma_l M32 (v inputByteLen) (as_seq_multi h0 ib) (v outputByteLen) (as_seq_multi h0 rb) 0

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
  let ib = ntup1 input in
  let rb = ntup1 output in
  let h0 = ST.get () in
  keccak #M32 absorb_inner_32 1152ul (* 448ul *) inputByteLen ib (byte 0x06) 28ul rb;
  sha3_224_lemma_l M32 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 0

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
  let ib = ntup1 input in
  let rb = ntup1 output in
  let h0 = ST.get () in
  keccak #M32 absorb_inner_32 1088ul (* 512ul *) inputByteLen ib (byte 0x06) 32ul rb;
  sha3_256_lemma_l M32 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 0

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
  let ib = ntup1 input in
  let rb = ntup1 output in
  let h0 = ST.get () in
  keccak #M32 absorb_inner_32 832ul (* 768ul *) inputByteLen ib (byte 0x06) 48ul rb;
  sha3_384_lemma_l M32 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 0

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
  let ib = ntup1 input in
  let rb = ntup1 output in
  let h0 = ST.get () in
  keccak #M32 absorb_inner_32 576ul (* 1024ul *) inputByteLen ib (byte 0x06) 64ul rb;
  sha3_512_lemma_l M32 (v inputByteLen) (as_seq_multi h0 ib) (as_seq_multi h0 rb) 0

[@@ Comment "Allocate state buffer of 200-bytes"]
inline_for_extraction
val state_malloc:
    r:rid
  -> ST.ST (s:buffer uint64 { length s = 25 })
  (requires (fun _ ->
    ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    live h1 s /\
    M.(modifies loc_none h0 h1) /\
    fresh_loc (loc_addr_of_buffer s) h0 h1 /\
    (M.loc_includes (M.loc_region_only true r) (loc_addr_of_buffer s)) /\
    freeable s))

let state_malloc r =
  malloc r (u64 0) 25ul

[@@ Comment "Free state buffer"]
val state_free:
    s:buffer uint64 { length s = 25 }
  -> ST.ST unit
  (requires fun h0 ->
    freeable s /\ live h0 s)
  (ensures fun h0 _ h1 ->
    M.modifies (loc_addr_of_buffer s) h0 h1)

let state_free s =
  free s

[@@ Comment "Absorb number of input blocks and write the output state

  This function is intended to receive a hash state and input buffer.
  It processes an input of multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block are ignored.

  The argument `state` (IN/OUT) points to hash state, i.e., uint64_t[25]
  The argument `input` (IN) points to `inputByteLen` bytes of valid memory,
  i.e., uint8_t[inputByteLen]"]
val shake128_absorb_nblocks:
  state:lbuffer_t MUT (vec_t U64 1) 25ul
  -> input:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h state /\ disjoint input state)
     (ensures  fun h0 _ h1 ->
       modifies (loc state) h0 h1 /\
       as_seq h1 state ==
          V.absorb_inner_nblocks #M32 168 (v inputByteLen) (as_seq_multi h0 (ntup1 input)) (as_seq h0 state))
let shake128_absorb_nblocks state input inputByteLen =
  absorb_inner_nblocks #M32 absorb_inner_32 168ul inputByteLen (ntup1 input) state

[@@ Comment "Absorb a final partial block of input and write the output state

  This function is intended to receive a hash state and input buffer.
  It processes a sequence of bytes at end of input buffer that is less
  than 168-bytes (SHAKE128 block size),
  any bytes of full blocks at start of input buffer are ignored.

  The argument `state` (IN/OUT) points to hash state, i.e., uint64_t[25]
  The argument `input` (IN) points to `inputByteLen` bytes of valid memory,
  i.e., uint8_t[inputByteLen]

  Note: Full size of input buffer must be passed to `inputByteLen` including
  the number of full-block bytes at start of input buffer that are ignored"]
val shake128_absorb_final:
  state:lbuffer_t MUT (vec_t U64 1) 25ul
  -> input:buffer_t MUT uint8
  -> inputByteLen:size_t{v inputByteLen == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h state /\ disjoint input state)
     (ensures  fun h0 _ h1 ->
       modifies (loc state) h0 h1 /\
       as_seq h1 state ==
         V.absorb_final #M32 (as_seq h0 state) 168 (v inputByteLen) (as_seq_multi h0 (ntup1 input)) (byte 0x1F))
let shake128_absorb_final state input inputByteLen =
  absorb_final #M32 absorb_inner_32 168ul inputByteLen (ntup1 input) (byte 0x1F) state

[@@ Comment "Squeeze a hash state to output buffer

  This function is intended to receive a hash state and output buffer.
  It produces an output of multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block are ignored.

  The argument `state` (IN) points to hash state, i.e., uint64_t[25]
  The argument `output` (OUT) points to `outputByteLen` bytes of valid memory,
  i.e., uint8_t[outputByteLen]"]
val shake128_squeeze_nblocks:
  state:lbuffer_t MUT (vec_t U64 1) 25ul
  -> output:buffer_t MUT uint8
  -> outputByteLen:size_t{v outputByteLen == length output}
  -> Stack unit
     (requires fun h ->
       live h output /\ live h state /\ disjoint output state)
     (ensures  fun h0 _ h1 ->
       modifies (loc state |+| loc output) h0 h1 /\
       (let s', b' =
          V.squeeze_nblocks #M32 168 (v outputByteLen) (as_seq h0 state, as_seq_multi h0 (ntup1 output)) in
          as_seq h1 state == s' /\
          as_seq_multi h1 (ntup1 output) == b'))
let shake128_squeeze_nblocks state output outputByteLen =
  squeeze_nblocks #M32 state 168ul outputByteLen (ntup1 output)

