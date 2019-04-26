module Hacl.SHA3

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.SHA3

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = Spec.SHA3

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val shake128_hacl:
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> outputByteLen:size_t
  -> output:lbuffer uint8 outputByteLen
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.shake128 (v inputByteLen) (as_seq h0 input) (v outputByteLen))
let shake128_hacl inputByteLen input outputByteLen output =
  keccak 1344ul 256ul inputByteLen input (byte 0x1F) outputByteLen output

val shake256_hacl:
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> outputByteLen:size_t
  -> output:lbuffer uint8 outputByteLen
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.shake256 (v inputByteLen) (as_seq h0 input) (v outputByteLen))
let shake256_hacl inputByteLen input outputByteLen output =
  keccak 1088ul 512ul inputByteLen input (byte 0x1F) outputByteLen output

val sha3_224:
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> output:lbuffer uint8 28ul
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_224 (v inputByteLen) (as_seq h0 input))
let sha3_224 inputByteLen input output =
  keccak 1152ul 448ul inputByteLen input (byte 0x06) 28ul output

val sha3_256:
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> output:lbuffer uint8 32ul
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_256 (v inputByteLen) (as_seq h0 input))
let sha3_256 inputByteLen input output =
  keccak 1088ul 512ul inputByteLen input (byte 0x06) 32ul output

val sha3_384:
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> output:lbuffer uint8 48ul
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_384 (v inputByteLen) (as_seq h0 input))
let sha3_384 inputByteLen input output =
  keccak 832ul 768ul inputByteLen input (byte 0x06) 48ul output

val sha3_512:
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> output:lbuffer uint8 64ul
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_512 (v inputByteLen) (as_seq h0 input))
let sha3_512 inputByteLen input output =
  keccak 576ul 1024ul inputByteLen input (byte 0x06) 64ul output

(* cSHAKE for Frodo *)
inline_for_extraction noextract
val cshake128_frodo:
    input_len:size_t
  -> input:lbuffer uint8 input_len
  -> cstm:uint16
  -> output_len:size_t
  -> output:lbuffer uint8 output_len
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ disjoint input output)
    (ensures  fun h0 _ h1 ->
      modifies (loc output) h0 h1 /\
      as_seq h1 output ==
      S.cshake128_frodo (v input_len) (as_seq h0 input) cstm (v output_len))
let cshake128_frodo input_len input cstm output_len output =
  push_frame ();
  let s = create 25ul (u64 0) in
  s.(0ul) <- u64 0x10010001a801 |. (to_u64 cstm <<. 48ul);
  state_permute s;
  absorb s 168ul input_len input (byte 0x04);
  squeeze s 168ul output_len output;
  pop_frame ()

inline_for_extraction noextract
val cshake256_frodo:
    input_len:size_t
  -> input:lbuffer uint8 input_len
  -> cstm:uint16
  -> output_len:size_t
  -> output:lbuffer uint8 output_len
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ disjoint input output)
    (ensures  fun h0 _ h1 ->
      modifies (loc output) h0 h1 /\
      as_seq h1 output ==
      S.cshake256_frodo (v input_len) (as_seq h0 input) cstm (v output_len))
let cshake256_frodo input_len input cstm output_len output =
  push_frame ();
  let s = create 25ul (u64 0) in
  s.(0ul) <- u64 0x100100018801 |. (to_u64 cstm <<. 48ul);
  state_permute s;
  absorb s 136ul input_len input (byte 0x04);
  squeeze s 136ul output_len output;
  pop_frame ()
