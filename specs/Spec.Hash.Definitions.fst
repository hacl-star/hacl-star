
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
type hash_alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512
  | SHA1
  | MD5
  | Blake2S
  | Blake2B
  | SHA3_256

inline_for_extraction noextract
let is_sha2 = function
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> true
  | _ -> false

inline_for_extraction noextract
let is_sha3 = function
  | SHA3_256 -> true
  | _ -> false

inline_for_extraction noextract
let is_blake = function
  | Blake2S | Blake2B -> true
  | _ -> false

inline_for_extraction noextract
let is_md = function
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> true
  | _ -> false

let sha2_alg = a:hash_alg { is_sha2 a }
let sha3_alg = a:hash_alg { is_sha3 a }
let blake_alg = a:hash_alg { is_blake a }
let md_alg = a:hash_alg { is_md a }

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

inline_for_extraction
let max_input_length: hash_alg -> option pos = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> Some (pow2 61 - 1)
  | SHA2_384 | SHA2_512 -> Some (pow2 125 - 1)
  | Blake2S -> Some (pow2 64 - 1)
  | Blake2B -> Some (pow2 128 - 1)
  | SHA3_256 -> None

let maxed_hash_alg = a:hash_alg { Some? (max_input_length a) }

let sha2_alg_is_maxed (a: hash_alg): Lemma (requires (is_sha2 a)) (ensures (Some? (max_input_length a))) [ SMTPat (is_sha2 a) ] = ()
let md_alg_is_maxed (a: hash_alg): Lemma (requires (is_md a)) (ensures (Some? (max_input_length a))) [ SMTPat (is_md a) ] = ()
let blake_alg_is_maxed (a: hash_alg): Lemma (requires (is_blake a)) (ensures (Some? (max_input_length a))) [ SMTPat (is_blake a) ] = ()

// TODO: many of these definitions are only used by the MD padding scheme,
// meaning they should be defined over md_alg!

(* A type that can hold a maximum length, in bits. *)
inline_for_extraction
let len_int_type: maxed_hash_alg -> inttype = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> U64
  | SHA2_384 | SHA2_512 -> U128
  | Blake2S -> U64
  | Blake2B -> U128

inline_for_extraction
let nat_to_len (a:maxed_hash_alg) (n:nat{n <= maxint (len_int_type a)}) =
  mk_int #(len_int_type a ) #PUB n

(* A type that can hold a maximum length, in bits. *)
inline_for_extraction
let len_t: hash_alg -> Type = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> pub_uint64
  | SHA2_384 | SHA2_512 -> pub_uint128
  | SHA3_256 -> unit
  | Blake2S -> pub_uint64
  | Blake2B -> pub_uint128

val len_v: a:maxed_hash_alg -> len_t a -> nat
let len_v = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> uint_v #U64 #PUB
  | SHA2_384 | SHA2_512 -> uint_v #U128 #PUB
  | Blake2S -> uint_v #U64 #PUB
  | Blake2B -> uint_v #U128 #PUB

(* Number of bytes occupied by a len_t, i.e. the size of the encoded length in
   the padding. *)
let len_length: maxed_hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 8
  | SHA2_384 | SHA2_512 -> 16
  | Blake2S -> 8
  | Blake2B -> 16

(* Same thing, as a machine integer *)
inline_for_extraction
let len_len: a:maxed_hash_alg -> Tot (n:size_t{v n = len_length a}) = function
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
  | SHA3_256 -> U64

inline_for_extraction
let row (a:blake_alg) = lseq (uint_t (word_t a) SEC) 4

inline_for_extraction
let word (a: hash_alg) = match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 | SHA3_256 -> uint_t (word_t a) SEC
  | Blake2S | Blake2B -> row a

(* In bytes *)
let word_length: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 8
  | SHA3_256 -> 8
  | Blake2S -> 4
  | Blake2B -> 8

(* Number of words for a block size *)

let block_word_length (a: hash_alg) =
  match a with
  | SHA3_256 -> normalize_term (1088 / 8 / 8) // 17
  | _ -> 16

(* Define the size block in bytes *)

let block_length a =
  let open FStar.Mul in
  word_length a * block_word_length a

(* Number of words for intermediate hash, i.e. the working state. *)
inline_for_extraction
let state_word_length a =
  match a with
  | MD5 -> 4
  | SHA1 -> 5
  | Blake2S | Blake2B -> 4
  | SHA3_256 -> 25
  | _ -> 8

inline_for_extraction
let extra_state a = match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 | SHA3_256 -> unit
  | Blake2S | Blake2B -> nat

(* The working state *)
inline_for_extraction
let words_state a = lseq (word a) (state_word_length a)

(* Number of words for final hash *)
inline_for_extraction
let hash_word_length: hash_alg -> Tot nat = function
  | MD5 -> 4
  | SHA1 -> 5
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA3_256 -> 4
  | SHA2_384 -> 6
  | SHA2_512 -> 8
  | Blake2S | Blake2B -> 8

(* Define the final hash length in bytes *)

let hash_length a =
  let open FStar.Mul in
  word_length a * hash_word_length a


(** Padding *)

(* Number of zeroes that should go into the padding *)
let pad0_length (a:md_alg) (len:nat): Tot (n:nat{(len + 1 + n + len_length a) % block_length a = 0}) =
  (block_length a - (len + len_length a + 1)) % block_length a

(* Total length for the padding, a.k.a. the suffix length. *)
let pad_length (a: md_alg) (len: nat): Tot (n:nat { (len + n) % block_length a = 0 }) =
  pad0_length a len + 1 + len_length a

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

let init_t (a: hash_alg) = words_state a

let update_t (a: md_alg) =
  h:words_state a ->
  l:bytes { Seq.length l = block_length a } ->
  words_state a

let less_than_max_input_length l a =
  match max_input_length a with
  | Some max -> l <= max
  | None -> true

let pad_t (a: md_alg) =
  l:nat { l `less_than_max_input_length` a } ->
  b:bytes { (Seq.length b + l) % block_length a = 0 }

let finish_t (a: hash_alg) =
  h:words_state a ->
  bytes_hash a
