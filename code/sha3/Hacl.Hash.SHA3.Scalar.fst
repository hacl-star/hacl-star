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
module V = Hacl.Spec.SHA3.Vec
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
let same_as x = y:size_t { x == y }

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

val state_free:
    s:buffer uint64 { length s = 25 }
  -> ST.ST unit
  (requires fun h0 ->
    freeable s /\ live h0 s)
  (ensures fun h0 _ h1 ->
    M.modifies (loc_addr_of_buffer s) h0 h1)

let state_free s =
  free s

open Lib.NTuple
open Lib.MultiBuffer
open Lib.IntVector

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
          V.absorb_inner_nblocks #Shake128 #M32 168 (v inputByteLen) (as_seq_multi h0 (ntup1 input)) (as_seq h0 state))
let shake128_absorb_nblocks state input inputByteLen =
  absorb_inner_nblocks #Shake128 #M32 168ul inputByteLen (ntup1 input) state

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
         V.absorb_final #Shake128 #M32 (as_seq h0 state) 168 (v inputByteLen) (as_seq_multi h0 (ntup1 input)) (byte 0x1F))
let shake128_absorb_final state input inputByteLen =
  absorb_final #Shake128 #M32 168ul inputByteLen (ntup1 input) (byte 0x1F) state

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
          V.squeeze_nblocks #Shake128 #M32 168 (v outputByteLen) (as_seq h0 state, as_seq_multi h0 (ntup1 output)) in
          as_seq h1 state == s' /\
          as_seq_multi h1 (ntup1 output) == b'))
let shake128_squeeze_nblocks state output outputByteLen =
  squeeze_nblocks #Shake128 #M32 state 168ul outputByteLen (ntup1 output)
