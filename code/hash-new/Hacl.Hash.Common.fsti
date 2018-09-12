module Hacl.Hash.Common

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = LowStar.Modifies
module B = LowStar.Buffer
module Spec = Spec.Hash.Common
open Spec.Hash.Helpers

(** We need to reveal the definition of the internal state for clients to use it *)

let word (a: hash_alg) =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> U32.t
  | SHA2_384 | SHA2_512 -> U64.t

type state (a: hash_alg) =
  b:B.buffer (word a) { B.length b = size_hash_w a }

inline_for_extraction
let size_word_ul (a: hash_alg): n:U32.t { U32.v n = size_word a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 4ul
  | SHA2_384 | SHA2_512 -> 8ul

inline_for_extraction
let size_block_ul (a: hash_alg): n:U32.t { U32.v n = size_block a } =
  U32.(size_word_ul a *^ 16ul)

inline_for_extraction
let size_len_ul (a: hash_alg): n:U32.t { U32.v n = size_len_8 a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 8ul
  | SHA2_384 | SHA2_512 -> 16ul


(** Padding, not specialized, to be inlined in a specialized caller instead. *)

inline_for_extraction
let pad_st (a: hash_alg) = len:len_t a -> dst:B.buffer U8.t ->
  ST.Stack unit
    (requires (fun h ->
      len_v a len < max_input8 a /\
      B.live h dst /\
      B.length dst = pad_length a (len_v a len)))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (Spec.pad a (len_v a len))))

noextract
val pad: a:hash_alg -> pad_st a

(* So that the caller can compute which length to allocate for padding. *)

val pad_len: a:hash_alg -> len:len_t a ->
  x:U32.t { U32.v x = pad_length a (len_v a len) }


(** Finish, not specialized, to be inlined in a specialized caller instead. *)

let hash_st (a: hash_alg) = b:B.buffer U8.t { B.length b = size_hash a }

inline_for_extraction
let finish_st (a: hash_alg) = s:state a -> dst:hash_st a -> ST.Stack unit
  (requires (fun h ->
    B.disjoint s dst /\
    B.live h s /\
    B.live h dst))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    Seq.equal (B.as_seq h1 dst) (Spec.Hash.Common.finish a (B.as_seq h0 s))))

noextract
val finish: a:hash_alg -> finish_st a
