module Hacl.Hash.Definitions

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = LowStar.Modifies
module B = LowStar.Buffer
module Spec = Spec.Hash.Common

open Spec.Hash.Helpers
open FStar.Mul

(** The low-level types that our clients need to be aware of, in order to
    successfully call this module. *)

inline_for_extraction
let word (a: hash_alg) =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> U32.t
  | SHA2_384 | SHA2_512 -> U64.t

inline_for_extraction
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

inline_for_extraction
let size_hash_final_w_ul (a: hash_alg): n:U32.t { U32.v n = size_hash_final_w a } =
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 -> 7ul
  | SHA2_256 -> 8ul
  | SHA2_384 -> 6ul
  | SHA2_512 -> 8ul

inline_for_extraction
let size_hash_ul (a: hash_alg): n:U32.t { U32.v n = size_hash a } =
  U32.(size_word_ul a *^ size_hash_final_w_ul a)

inline_for_extraction
let blocks_t (a: hash_alg) =
  b:B.buffer U8.t { B.length b % size_block a = 0 }

let hash_t (a: hash_alg) = b:B.buffer U8.t { B.length b = size_hash a }


(** The types of all stateful operations for a hash algorithm. *)

inline_for_extraction
let alloca_st (a: hash_alg) = unit -> ST.StackInline (state a)
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 s h1 ->
    M.(modifies M.loc_none h0 h1) /\
    B.live h1 s /\
    B.frameOf s == HS.get_tip h0 /\
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

// Note: we cannot take more than 4GB of data because we are currently
// constrained by the size of buffers...
inline_for_extraction
let update_multi_st (a: hash_alg) =
  s:state a ->
  blocks:blocks_t a ->
  n:U32.t { B.length blocks = size_block a * U32.v n } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h blocks /\ B.disjoint s blocks))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      Seq.equal (B.as_seq h1 s)
        (Spec.Hash.update_multi a (B.as_seq h0 s) (B.as_seq h0 blocks))))

inline_for_extraction
let update_last_st (a: hash_alg) =
  s:state a ->
  prev_len:len_t a { len_v a prev_len % size_block a = 0 } ->
  input:B.buffer U8.t { B.length input + len_v a prev_len < max_input8 a } ->
  input_len:U32.t { B.length input = U32.v input_len } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h input /\ B.disjoint s input))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      Seq.equal (B.as_seq h1 s)
        (Spec.Hash.Incremental.update_last a (B.as_seq h0 s) (len_v a prev_len) (B.as_seq h0 input))))

inline_for_extraction
let finish_st (a: hash_alg) = s:state a -> dst:hash_t a -> ST.Stack unit
  (requires (fun h ->
    B.disjoint s dst /\
    B.live h s /\
    B.live h dst))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    Seq.equal (B.as_seq h1 dst) (Spec.Hash.Common.finish a (B.as_seq h0 s))))

inline_for_extraction
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

