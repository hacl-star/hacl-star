module Spec.Hash.Definitions

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

let is_sha2 = function
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> true
  | _ -> false

let sha2_alg = a:hash_alg { is_sha2 a }


(** Maximum input data length. *)

(* In bytes. *)
inline_for_extraction noextract
let max_input_length: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> pow2 61
  | SHA2_384 | SHA2_512 -> pow2 125

(* A type that can hold a maximum length, in bits. *)
inline_for_extraction
let len_t: hash_alg -> Type = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> UInt64.t
  | SHA2_384 | SHA2_512 -> UInt128.t

val len_v: a:hash_alg -> len_t a -> nat
let len_v = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> UInt64.v
  | SHA2_384 | SHA2_512 -> UInt128.v

(* Number of bytes occupied by a len_t, i.e. the size of the encoded length in
   the padding. *)
let len_length: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 8
  | SHA2_384 | SHA2_512 -> 16

(* Same thing, as a machine integer *)
inline_for_extraction
let len_len: a:hash_alg -> Tot (n:UInt32.t{UInt32.v n = len_length a}) = function
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 8ul
  | SHA2_384 | SHA2_512 -> 16ul

(** Working state of the algorithms. *)

(* Internally, hash functions operate on a series of machine words. *)
inline_for_extraction
let word: hash_alg -> Tot Type0 = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> UInt32.t
  | SHA2_384 | SHA2_512 -> UInt64.t

(* In bytes *)
let word_length: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 8

(* Number of words for a block size *)
noextract
let block_word_length = 16

(* Define the size block in bytes *)
noextract
let block_length a =
  let open FStar.Mul in
  word_length a * block_word_length

(* Number of words for intermediate hash, i.e. the working state. *)
inline_for_extraction noextract
let state_word_length a =
  match a with
  | MD5 -> 4
  | SHA1 -> 5
  | _ -> 8

(* The working state *)
let words_state a = m:Seq.seq (word a) {Seq.length m = state_word_length a}

(* Number of words for final hash *)
inline_for_extraction
let hash_word_length: hash_alg -> Tot nat = function
  | MD5 -> 4
  | SHA1 -> 5
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA2_384 -> 6
  | SHA2_512 -> 8

(* Define the final hash length in bytes *)
noextract
let hash_length a =
  let open FStar.Mul in
  word_length a * hash_word_length a


(** Padding *)

(* Number of zeroes that should go into the padding *)
let pad0_length (a:hash_alg) (len:nat): Tot (n:nat{(len + 1 + n + len_length a) % block_length a = 0}) =
  (block_length a - (len + len_length a + 1)) % block_length a

(* Total length for the padding, a.k.a. the suffix length. *)
let pad_length (a: hash_alg) (len: nat): Tot (n:nat { (len + n) % block_length a = 0 }) =
  pad0_length a len + 1 + len_length a

(** Endian-ness *)

module E = FStar.Kremlin.Endianness

let lbytes (l:nat) = b:Seq.seq UInt8.t {Seq.length b = l}

(* Define word based operators *)
let bytes_of_words: a:hash_alg -> Tot (s:Seq.seq (word a) -> Tot (lbytes FStar.Mul.(word_length a * Seq.length s))) = function
  | MD5 -> E.le_of_seq_uint32
  | SHA1 | SHA2_224 | SHA2_256 -> E.be_of_seq_uint32
  | SHA2_384 | SHA2_512 -> E.be_of_seq_uint64

let words_of_bytes: a:hash_alg -> Tot (len:nat -> b:lbytes FStar.Mul.(word_length a * len) -> Tot (s:Seq.seq (word a){Seq.length s = len})) = function
  | MD5 -> E.seq_uint32_of_le
  | SHA1 | SHA2_224 | SHA2_256 -> E.seq_uint32_of_be
  | SHA2_384 | SHA2_512 -> E.seq_uint64_of_be


(** The data format taken and returned by the hash specifications. *)

(* Input data. *)
type bytes =
  m:Seq.seq UInt8.t

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
  h':words_state a

let pad_t (a: hash_alg) =
  l:nat { l < max_input_length a } ->
  b:bytes { (Seq.length b + l) % block_length a = 0 }

let finish_t (a: hash_alg) =
  h:words_state a ->
  bytes_hash a
