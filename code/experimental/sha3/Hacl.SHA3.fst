module Hacl.SHA3

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer
open Lib.Endianness

open Hacl.Impl.SHA3

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val shake128:
     inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 -> modifies (loc_buffer output) h0 h1)
let shake128 inputByteLen input outputByteLen output =
  keccak (size 1344) (size 256) inputByteLen input (u8 0x1F) outputByteLen output

val shake256:
     inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 -> modifies (loc_buffer output) h0 h1)
let shake256 inputByteLen input outputByteLen output =
  keccak (size 1088) (size 512) inputByteLen input (u8 0x1F) outputByteLen output

val sha3_224:
     inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> output:lbytes 28
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 -> modifies (loc_buffer output) h0 h1)
let sha3_224 inputByteLen input output =
  keccak (size 1152) (size 448) inputByteLen input (u8 0x06) (size 28) output

val sha3_256:
     inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> output:lbytes 32
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 -> modifies (loc_buffer output) h0 h1)
let sha3_256 inputByteLen input output =
  keccak (size 1088) (size 512) inputByteLen input (u8 0x06) (size 32) output

val sha3_384:
     inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> output:lbytes 48
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 -> modifies (loc_buffer output) h0 h1)
let sha3_384 inputByteLen input output =
  keccak (size 832) (size 768) inputByteLen input (u8 0x06) (size 48) output

val sha3_512:
     inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> output:lbytes 64
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 -> modifies (loc_buffer output) h0 h1)
let sha3_512 inputByteLen input output =
  keccak (size 576) (size 1024) inputByteLen input (u8 0x06) (size 64) output
