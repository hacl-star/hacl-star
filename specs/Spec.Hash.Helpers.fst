module Spec.Hash.Helpers

(* This module contains shared definitions across all hash algorithms. It
 * defines a common, shared `hash_alg` type, along with word sizes, type of the
 * working state, and other helpers. It also defines the type of the core functions
 * init / update / pad / finish that any algorithm must implement in order to be
 * turned into a complete hash construction. *)

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
let max_input8: hash_alg -> Tot nat = function
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
let size_len_8: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 8
  | SHA2_384 | SHA2_512 -> 16

(* Same thing, as a machine integer *)
inline_for_extraction
let size_len_ul_8: a:hash_alg -> Tot (n:UInt32.t{UInt32.v n = size_len_8 a}) = function
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 8ul
  | SHA2_384 | SHA2_512 -> 16ul

(* A useful lemma for all the operations that involve going from bytes to bits. *)
let max_input_size_len (a: hash_alg): Lemma
  (ensures FStar.Mul.(max_input8 a * 8 = pow2 (size_len_8 a * 8)))
=
  let open FStar.Mul in
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 ->
      assert_norm (max_input8 a * 8 = pow2 (size_len_8 a * 8))
  | SHA2_384 | SHA2_512 ->
      assert_norm (max_input8 a * 8 = pow2 (size_len_8 a * 8))


(** Working state of the algorithms. *)

(* Internally, hash functions operate on a series of machine words. *)
inline_for_extraction
let word: hash_alg -> Tot Type0 = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> UInt32.t
  | SHA2_384 | SHA2_512 -> UInt64.t

(* In bytes *)
let size_word: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 8

(* Number of words for a block size *)
let size_block_w = 16

(* Define the size block in bytes *)
let size_block a =
  let open FStar.Mul in
  size_word a * size_block_w

(* Number of words for intermediate hash, i.e. the working state. *)
inline_for_extraction noextract
let size_hash_w a =
  match a with
  | MD5 -> 4
  | SHA1 -> 5
  | _ -> 8

(* The working state *)
let hash_w a = m:Seq.seq (word a) {Seq.length m = size_hash_w a}

(* Number of words for final hash *)
inline_for_extraction
let size_hash_final_w: hash_alg -> Tot nat = function
  | MD5 -> 4
  | SHA1 -> 5
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA2_384 -> 6
  | SHA2_512 -> 8

(* Define the final hash length in bytes *)
let size_hash a =
  let open FStar.Mul in
  size_word a * size_hash_final_w a


(** Padding *)

(* Number of zeroes that should go into the padding *)
let pad0_length (a:hash_alg) (len:nat): Tot (n:nat{(len + 1 + n + size_len_8 a) % size_block a = 0}) =
  (size_block a - (len + size_len_8 a + 1)) % size_block a

(* Total length for the padding, a.k.a. the suffix length. *)
let pad_length (a: hash_alg) (len: nat): Tot (n:nat { (len + n) % size_block a = 0 }) =
  pad0_length a len + 1 + size_len_8 a

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let pad_invariant_block (a: hash_alg) (blocks: nat) (rest: nat): Lemma
  (requires blocks % size_block a = 0)
  (ensures (pad_length a rest = pad_length a (blocks + rest)))
  [ SMTPat (pad_length a (blocks + rest)) ]
=
  ()
#pop-options

(** Endian-ness *)

module E = FStar.Kremlin.Endianness

let lbytes (l:nat) = b:Seq.seq UInt8.t {Seq.length b = l}

(* Define word based operators *)
let bytes_of_words: a:hash_alg -> Tot (s:Seq.seq (word a) -> Tot (lbytes FStar.Mul.(size_word a * Seq.length s))) = function
  | MD5 -> E.le_of_seq_uint32
  | SHA1 | SHA2_224 | SHA2_256 -> E.be_of_seq_uint32
  | SHA2_384 | SHA2_512 -> E.be_of_seq_uint64

let words_of_bytes: a:hash_alg -> Tot (len:nat -> b:lbytes FStar.Mul.(size_word a * len) -> Tot (s:Seq.seq (word a){Seq.length s = len})) = function
  | MD5 -> E.seq_uint32_of_le
  | SHA1 | SHA2_224 | SHA2_256 -> E.seq_uint32_of_be
  | SHA2_384 | SHA2_512 -> E.seq_uint64_of_be


(** The data format taken and returned by the hash specifications. *)

(* Input data. *)
type bytes =
  m:Seq.seq UInt8.t

(* Input data, multiple of a block length. *)
let bytes_block a =
  l:bytes { Seq.length l = size_block a }

(* Input data, multiple of a block length. *)
let bytes_blocks a =
  l:bytes { Seq.length l % size_block a = 0 }

(* Output data, i.e. the final hash (tag). *)
let bytes_hash a =
  b:bytes { Seq.length b = size_hash a }


(** The types for the core functions *)

let init_t (a: hash_alg) =
  hash_w a

let update_t (a: hash_alg) =
  h:hash_w a ->
  l:bytes { Seq.length l = size_block a } ->
  h':hash_w a

let pad_t (a: hash_alg) =
  l:nat { l < max_input8 a } ->
  b:bytes { (Seq.length b + l) % size_block a = 0 }

let finish_t (a: hash_alg) =
  h:hash_w a ->
  bytes_hash a
