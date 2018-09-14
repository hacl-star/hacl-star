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

(** The type of init, alloca and update, share by all algorithms. Note that
    since we manage to hide the static footprints, all algorithms do have a generic
    signature. *)

inline_for_extraction
let alloca_st (a: hash_alg) = unit -> ST.StackInline (state a)
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 s h1 ->
    M.(modifies M.loc_none h0 h1) /\
    B.live h1 s /\
    Seq.equal (B.as_seq h1 s) (Spec.Hash.init a) /\
    LowStar.Monotonic.Buffer.alloc_post_mem_common s h0 h1 (Spec.Hash.init a)))

inline_for_extraction
let init_st (a: hash_alg) = s:state a -> ST.Stack unit
  (requires (fun h ->
    B.live h s))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer s) h0 h1) /\
    Seq.equal (B.as_seq h1 s) (Spec.Hash.init a)))

inline_for_extraction
let update_st (a: hash_alg) =
  s:state a ->
  block:B.buffer U8.t { B.length block = size_block a } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h block /\ B.disjoint s block))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer s) h0 h1) /\
      Seq.equal (B.as_seq h1 s) (Spec.Hash.update a (B.as_seq h0 s) (B.as_seq h0 block))))


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

let hash_t (a: hash_alg) = b:B.buffer U8.t { B.length b = size_hash a }

inline_for_extraction
let finish_st (a: hash_alg) = s:state a -> dst:hash_t a -> ST.Stack unit
  (requires (fun h ->
    B.disjoint s dst /\
    B.live h s /\
    B.live h dst))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    Seq.equal (B.as_seq h1 dst) (Spec.Hash.Common.finish a (B.as_seq h0 s))))

noextract
val finish: a:hash_alg -> finish_st a


(** The whole hash algorithm *)

let hash_st (a: hash_alg) =
  input:B.buffer U8.t ->
  input_len:U32.t { B.length input = U32.v input_len } ->
  dst:hash_t a ->
  ST.Stack unit
    (requires (fun h ->
      B.live h input /\
      B.live h dst /\
      B.disjoint input dst /\
      B.length input < max_input8 a))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (Spec.Hash.Nist.hash a (B.as_seq h0 input))))
