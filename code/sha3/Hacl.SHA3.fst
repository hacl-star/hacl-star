module Hacl.SHA3

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.SHA3

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module S = Spec.SHA3

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val shake128_hacl:
    inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc_buffer output) h0 h1 /\
       as_seq h1 output ==
       S.shake128 (v inputByteLen) (as_seq h0 input) (v outputByteLen))
let shake128_hacl inputByteLen input outputByteLen output =
  keccak (size 1344) (size 256) inputByteLen input (byte 0x1F) outputByteLen output

val shake256_hacl:
    inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> outputByteLen:size_t
  -> output:lbytes (v outputByteLen)
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc_buffer output) h0 h1 /\
       as_seq h1 output ==
       S.shake256 (v inputByteLen) (as_seq h0 input) (v outputByteLen))
let shake256_hacl inputByteLen input outputByteLen output =
  keccak (size 1088) (size 512) inputByteLen input (byte 0x1F) outputByteLen output

val sha3_224:
    inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> output:lbytes 28
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc_buffer output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_224 (v inputByteLen) (as_seq h0 input))
let sha3_224 inputByteLen input output =
  keccak (size 1152) (size 448) inputByteLen input (byte 0x06) (size 28) output

val sha3_256:
    inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> output:lbytes 32
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc_buffer output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_256 (v inputByteLen) (as_seq h0 input))
let sha3_256 inputByteLen input output =
  keccak (size 1088) (size 512) inputByteLen input (byte 0x06) (size 32) output

val sha3_384:
    inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> output:lbytes 48
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc_buffer output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_384 (v inputByteLen) (as_seq h0 input))
let sha3_384 inputByteLen input output =
  keccak (size 832) (size 768) inputByteLen input (byte 0x06) (size 48) output

val sha3_512:
    inputByteLen:size_t
  -> input:lbytes (v inputByteLen)
  -> output:lbytes 64
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc_buffer output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_512 (v inputByteLen) (as_seq h0 input))
let sha3_512 inputByteLen input output =
  keccak (size 576) (size 1024) inputByteLen input (byte 0x06) (size 64) output

(* cSHAKE for Frodo *)
inline_for_extraction noextract
val cshake128_frodo:
    input_len:size_t
  -> input:lbuffer uint8 (v input_len)
  -> cstm:uint16
  -> output_len:size_t
  -> output:lbuffer uint8 (v output_len)
  -> Stack unit
    (requires fun h -> B.live h input /\ B.live h output /\ B.disjoint input output)
    (ensures  fun h0 _ h1 -> 
      modifies (loc_buffer output) h0 h1 /\
      as_seq h1 output ==
      S.cshake128_frodo (v input_len) (as_seq h0 input) cstm (v output_len))
let cshake128_frodo input_len input cstm output_len output =
  push_frame ();
  let s = create (size 25) (u64 0) in
  s.(size 0) <- u64 0x10010001a801 |. (to_u64 cstm <<. size 48);
  state_permute s;
  absorb s (size 168) input_len input (byte 0x04);
  squeeze s (size 168) output_len output;
  pop_frame ()

inline_for_extraction noextract
val cshake256_frodo:
    input_len:size_t
  -> input:lbuffer uint8 (v input_len)
  -> cstm:uint16
  -> output_len:size_t
  -> output:lbuffer uint8 (v output_len)
  -> Stack unit
    (requires fun h -> B.live h input /\ B.live h output /\ B.disjoint input output)
    (ensures  fun h0 _ h1 -> 
      modifies (loc_buffer output) h0 h1 /\
      as_seq h1 output ==
      S.cshake256_frodo (v input_len) (as_seq h0 input) cstm (v output_len))
let cshake256_frodo input_len input cstm output_len output =
  push_frame ();
  let s = create (size 25) (u64 0) in
  s.(size 0) <- u64 0x100100018801 |. (to_u64 cstm <<. size 48);
  state_permute s;
  absorb s (size 136) input_len input (byte 0x04);
  squeeze s (size 136) output_len output;
  pop_frame ()
