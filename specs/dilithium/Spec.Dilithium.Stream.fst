module Spec.Dilithium.Stream

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


open Spec.Dilithium.Params

module SHA3 = Spec.SHA3

type stream_t =
  | Shake128 | Shake256


(* same as SHA3.squeeze but it also gives s back
however, writing this to take blocks:nat{blocks<200} directly requires high rlimit
and makes test(sh:stream_t) = assert (sh = Shake128 || sh = Shake256) fail somehow, ???

Want to have: assert(keccak_squeeze_blocks ... = SHA3.shake256 ...)
*)
// val keccak_squeeze_bytes:
//     s: SHA3.state
//   -> rateInBytes:nat{rateInBytes > 0 /\ rateInBytes <= 200}
//   -> outBytes:size_nat
//   -> Tot (SHA3.state & lbytes outBytes)

// let keccak_squeeze_bytes s rateInBytes outBytes =
//   let outBlocks = outBytes / rateInBytes in
//   let a (i:nat{i <= outBlocks}) = SHA3.state in
//   let s, output =
//     generate_blocks rateInBytes outBlocks outBlocks a
//       (SHA3.squeeze_inner rateInBytes outBytes) s
//   in
//   let remOut = outBytes % rateInBytes in
//   let block = SHA3.storeState remOut s in
//   s, ((to_lseq output) @| block)

#set-options "--fuel 2 --ifuel 2 --z3rlimit 100"

val keccak_squeeze_blocks:
    s: SHA3.state
  -> rateInBytes:nat{rateInBytes > 0 /\ rateInBytes <= 200}
  -> outBlocks:size_nat{outBlocks < 1000}
  -> Tot (SHA3.state & lbytes (outBlocks * rateInBytes))

let keccak_squeeze_blocks s rateInBytes outBlocks =
  let a (i:nat{i <= outBlocks}) = SHA3.state in
  assert (a outBlocks == SHA3.state);
  let s, output = generate_blocks rateInBytes outBlocks outBlocks a
    (SHA3.squeeze_inner rateInBytes (outBlocks*rateInBytes)) s in
  s, to_lseq output

  // keccak_squeeze_bytes s rateInBytes (outBlocks * rateInBytes)


let new_stream: SHA3.state = create 25 (u64 0)

let shake128_absorb s n buf = SHA3.absorb s shake128_rate n buf (byte 0x1F)
let shake256_absorb s n buf = SHA3.absorb s shake256_rate n buf (byte 0x1F)
let shake128_squeeze s nblocks = keccak_squeeze_blocks s shake128_rate nblocks
let shake256_squeeze s nblocks = keccak_squeeze_blocks s shake256_rate nblocks
// let shake128_squeeze_bytes s n = keccak_squeeze_bytes s shake128_rate n
// let shake256_squeeze_bytes s n = keccak_squeeze_bytes s shake256_rate n


let stream_rate (stream:stream_t) =
  match stream with
  | Shake128 -> shake128_rate
  | Shake256 -> shake256_rate


let stream_absorb (stream:stream_t) =
  match stream with
  | Shake128 -> shake128_absorb
  | Shake256 -> shake256_absorb


val stream_squeeze:
    stream: stream_t
  -> s: SHA3.state
  -> nblocks: nat{nblocks < 1000}
  -> Tot (SHA3.state & lbytes (nblocks * stream_rate stream))

let stream_squeeze (stream:stream_t) (s:SHA3.state) (nblocks:nat{nblocks < 1000}) =
  match stream with
    | Shake128 -> shake128_squeeze s nblocks
    | Shake256 -> shake256_squeeze s nblocks


let crh seedlen seed = SHA3.shake256 seedlen seed crhbytes
