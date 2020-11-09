module Spec.Hash.Definitions

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

(* This module contains shared definitions across all hash algorithms. It
 * defines a common, shared `hash_alg` type, along with word sizes, type of the
 * working state, and other helpers. It also defines the type of the core functions
 * init / update / pad / finish that any algorithm must implement in order to be
 * turned into a complete hash construction.
 *
 * Some notes about terminology:
 * - this module uses the HACL* naming convention, namely init/update/finish
 *   (Cédric uses init/compress/extract in EverCrypt.HMAC and above)
 * - this module defines maximum lengths to be *bounds* (i.e. max_value + 1), a
 *   somewhat dubious convention that persists for historical reasons, but that
 *   is abandoned in miTLS via an extra indirection
 *
 * The following naming conventions are (tentatively) enforced.
 * - underscores (no camelCase)
 * - suffixes: _length for nat, _len for machine integer
 * - by default, lengths are in bytes; we use _word_length or _bit_len as suffixes
 * - for names that might conflict with their stateful counterparts, we prefix
 *   with the type, e.g. words_state or bytes_block
 *)

(** Supported hash algorithms. *)
// BB. This needs to be renamed...
type hash_alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512
  | SHA1
  | MD5
  | Blake2S
  | Blake2B

// BB. Remove when renamed.
let algorithm = hash_alg

let is_sha2 = function
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> true
  | _ -> false

 inline_for_extraction
let is_blake = function
  | Blake2S | Blake2B -> true
  | _ -> false

let is_md = function
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> true
  | _ -> false

let sha2_alg = a:hash_alg { is_sha2 a }
let blake_alg = a:hash_alg { is_blake a }

 inline_for_extraction
let to_blake_alg (a:blake_alg) = match a with
  | Blake2S -> Spec.Blake2.Blake2S
  | Blake2B -> Spec.Blake2.Blake2B

 inline_for_extraction
let to_hash_alg (a : Spec.Blake2.alg) =
  match a with
  | Spec.Blake2.Blake2S -> Blake2S
  | Spec.Blake2.Blake2B -> Blake2B

(** Maximum input data length. *)

(* In bytes. *)

// BB. Needs to be renamed...
inline_for_extraction 
let max_input_length: hash_alg -> Tot pos = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> pow2 61 - 1
  | SHA2_384 | SHA2_512 -> pow2 125 - 1
  | Blake2S -> pow2 64 - 1
  | Blake2B -> pow2 128 - 1

// BB. Removed once renamed...
let max_input = max_input_length

(* A type that can hold a maximum length, in bits. *)
inline_for_extraction
let len_int_type: hash_alg -> inttype = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> U64
  | SHA2_384 | SHA2_512 -> U128
  | Blake2S -> U64
  | Blake2B -> U128

inline_for_extraction
let nat_to_len (a:hash_alg) (n:nat{n <= maxint (len_int_type a)}) =
  mk_int #(len_int_type a ) #PUB n

(* A type that can hold a maximum length, in bits. *)
inline_for_extraction
let len_t: hash_alg -> Type = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> pub_uint64
  | SHA2_384 | SHA2_512 -> pub_uint128
  | Blake2S -> pub_uint64
  | Blake2B -> pub_uint128

val len_v: a:hash_alg -> len_t a -> nat
let len_v = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> uint_v #U64 #PUB
  | SHA2_384 | SHA2_512 -> uint_v #U128 #PUB
  | Blake2S -> uint_v #U64 #PUB
  | Blake2B -> uint_v #U128 #PUB

(* Number of bytes occupied by a len_t, i.e. the size of the encoded length in
   the padding. *)
let len_length: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 8
  | SHA2_384 | SHA2_512 -> 16
  | Blake2S -> 8
  | Blake2B -> 16

(* Same thing, as a machine integer *)
inline_for_extraction
let len_len: a:hash_alg -> Tot (n:size_t{v n = len_length a}) = function
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 8ul
  | SHA2_384 | SHA2_512 -> 16ul
  | Blake2S -> 8ul
  | Blake2B -> 16ul

(** Working state of the algorithms. *)

(* Internally, hash functions operate on a series of machine words. *)
inline_for_extraction
let word_t: hash_alg -> Tot inttype = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> U32
  | SHA2_384 | SHA2_512 -> U64
  | Blake2S -> U32
  | Blake2B -> U64

inline_for_extraction
let row (a:blake_alg) = lseq (uint_t (word_t a) SEC) 4

inline_for_extraction
let word (a: hash_alg) = match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> uint_t (word_t a) SEC
  | Blake2S | Blake2B -> row a

(* In bytes *)
let word_length: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 8
  | Blake2S -> 4
  | Blake2B -> 8

(* Number of words for a block size *)

let block_word_length = 16

(* Define the size block in bytes *)
// BB. Needs to be renamed

let block_length a =
  let open FStar.Mul in
  word_length a * block_word_length

// BB. Removed once renamed
let size_block = block_length

(* Number of words for intermediate hash, i.e. the working state. *)
inline_for_extraction 
let state_word_length a =
  match a with
  | MD5 -> 4
  | SHA1 -> 5
  | Blake2S | Blake2B -> 4
  | _ -> 8

inline_for_extraction 
let extra_state a = match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> unit
  // Directly storing the length instead of the number of blocks to avoid
  // nonlinear operations in the spec
  // We use uints to avoid reasoning about max bounds.
  // In practice, we never have overflows because of restrictions on length of buffers
  | Blake2S -> uint_t U64 SEC
  | Blake2B -> uint_t U128 SEC

inline_for_extraction 
let extra_state_v (#a:hash_alg) (s:extra_state a) : nat =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> 0
  | Blake2S -> v #U64 #SEC s
  | Blake2B -> v #U128 #SEC s

inline_for_extraction 
let extra_state_int_type : a:hash_alg{is_blake a} -> inttype = function
  | Blake2S -> U64
  | Blake2B -> U128

inline_for_extraction 
let extra_state_int_t (a:hash_alg{is_blake a}) : Type0 =
  int_t (extra_state_int_type a) SEC


let max_extra_state (a:hash_alg{is_blake a}) : nat =
  maxint (extra_state_int_type a)

// Do not use this in Low* code: it is not possible to directly convert a
// constant nat to a uint128.

let nat_to_extra_state (a:hash_alg{is_blake a}) (n:nat{n <= max_extra_state a}) :
  extra_state a =
  match a with
  | Blake2S -> mk_int #U64 #SEC n
  | Blake2B -> mk_int #U128 #SEC n

inline_for_extraction 
let extra_state_add_nat (#a:hash_alg{is_blake a}) (s : extra_state a)
                        (n:nat{n <= maxint (extra_state_int_type a)}) :
  extra_state a =
  (s <: extra_state_int_t a) +. nat_to_extra_state a n

inline_for_extraction 
let extra_state_add_size_t (#a:hash_alg{is_blake a}) (s : extra_state a) (n : size_t) :
  s':extra_state a{s' == extra_state_add_nat s (size_v n)} =
  (s <: extra_state_int_t a) +. (cast (extra_state_int_type a) SEC n)

(* The working state *)
inline_for_extraction 
let words_state' a = m:Seq.seq (word a) {Seq.length m = state_word_length a}

let words_state a = words_state' a & extra_state a

(* Number of words for final hash *)
inline_for_extraction
let hash_word_length: hash_alg -> Tot nat = function
  | MD5 -> 4
  | SHA1 -> 5
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA2_384 -> 6
  | SHA2_512 -> 8
  | Blake2S | Blake2B -> 8

(* Define the final hash length in bytes *)
// BB. Needs to be renamed

let hash_length a =
  let open FStar.Mul in
  word_length a * hash_word_length a

// BB. Removed once renamed
let size_hash = hash_length


(** Padding *)

(* Number of zeroes that should go into the padding *)
let pad0_length (a:hash_alg{is_md a}) (len:nat): Tot (n:nat{(len + 1 + n + len_length a) % block_length a = 0}) =
  (block_length a - (len + len_length a + 1)) % block_length a

(* Total length for the padding, a.k.a. the suffix length. *)
let pad_length (a: hash_alg) (len: nat): Tot (n:nat { (len + n) % block_length a = 0 }) =
  if is_blake a then (block_length a - len) % block_length a
  else pad0_length a len + 1 + len_length a

(** Endian-ness *)

(* Define word based operators *)
let bytes_of_words: a:hash_alg{is_md a} -> Tot (#len:size_nat{FStar.Mul.(len * word_length a) <= max_size_t} -> s:lseq (word a) len -> Tot (lbytes FStar.Mul.(word_length a * len))) = function
  | MD5 -> Lib.ByteSequence.uints_to_bytes_le #U32 #SEC
  | SHA1 | SHA2_224 | SHA2_256 -> Lib.ByteSequence.uints_to_bytes_be #U32 #SEC
  | SHA2_384 | SHA2_512 -> Lib.ByteSequence.uints_to_bytes_be #U64 #SEC

let words_of_bytes: a:hash_alg{is_md a} -> Tot (#len:size_nat{FStar.Mul.(len * word_length a) <= max_size_t} -> b:lbytes FStar.Mul.(word_length a * len) -> Tot (lseq (word a) len)) = function
  | MD5 -> Lib.ByteSequence.uints_from_bytes_le #U32 #SEC
  | SHA1 | SHA2_224 | SHA2_256 -> Lib.ByteSequence.uints_from_bytes_be #U32 #SEC
  | SHA2_384 | SHA2_512 -> Lib.ByteSequence.uints_from_bytes_be #U64 #SEC

(** The data format taken and returned by the hash specifications. *)

(* Input data. *)
type bytes = Seq.seq uint8

(* Input data, multiple of a block length. *)
let bytes_block a =
  l:bytes { Seq.length l = block_length a }

(* Input data, multiple of a block length. *)
let bytes_blocks a =
  l:bytes { Seq.length l % block_length a = 0 }

(* Output data, i.e. the final hash (tag). *)
let bytes_hash a =
  b:bytes { Seq.length b = hash_length a }

(** The types for the core functions *)

let init_t (a: hash_alg) =
  words_state a

let update_t (a: hash_alg) =
  h:words_state a ->
  l:bytes { Seq.length l = block_length a } ->
  words_state a

let pad_t (a: hash_alg) =
  l:nat { l <= max_input_length a } ->
  b:bytes { (Seq.length b + l) % block_length a = 0 }

let finish_t (a: hash_alg) =
  h:words_state a ->
  bytes_hash a
