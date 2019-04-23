module Hacl.Hash.Definitions

open Lib.IntTypes
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = LowStar.Modifies
module B = LowStar.Buffer
module Spec = Spec.Hash.PadFinish

open Spec.Hash.Definitions
open FStar.Mul

(** The low-level types that our clients need to be aware of, in order to
    successfully call this module. *)

inline_for_extraction
type state (a: hash_alg) =
  b:B.buffer (word a) { B.length b = state_word_length a }

inline_for_extraction
let word_len (a: hash_alg): n:size_t { v n = word_length a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 4ul
  | SHA2_384 | SHA2_512 -> 8ul

inline_for_extraction
let block_len (a: hash_alg): n:size_t { v n = block_length a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 64ul
  | SHA2_384 | SHA2_512 -> 128ul

inline_for_extraction
let hash_word_len (a: hash_alg): n:size_t { v n = hash_word_length a } =
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 -> 7ul
  | SHA2_256 -> 8ul
  | SHA2_384 -> 6ul
  | SHA2_512 -> 8ul

inline_for_extraction
let hash_len (a: hash_alg): n:size_t { v n = hash_length a } =
  match a with
  | MD5 -> 16ul
  | SHA1 -> 20ul
  | SHA2_224 -> 28ul
  | SHA2_256 -> 32ul
  | SHA2_384 -> 48ul
  | SHA2_512 -> 64ul

inline_for_extraction
let blocks_t (a: hash_alg) =
  b:B.buffer uint8 { B.length b % block_length a = 0 }

let hash_t (a: hash_alg) = b:B.buffer uint8 { B.length b = hash_length a }


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
  block:B.buffer uint8 { B.length block = block_length a } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h block /\ B.disjoint s block))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer s) h0 h1) /\
      Seq.equal (B.as_seq h1 s) (Spec.Hash.update a (B.as_seq h0 s) (B.as_seq h0 block))))

inline_for_extraction
let pad_st (a: hash_alg) = len:len_t a -> dst:B.buffer uint8 ->
  ST.Stack unit
    (requires (fun h ->
      len_v a len < max_input_length a /\
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
  n:size_t { B.length blocks = block_length a * v n } ->
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
  prev_len:len_t a { len_v a prev_len % block_length a = 0 } ->
  input:B.buffer uint8 { B.length input + len_v a prev_len < max_input_length a } ->
  input_len:size_t { B.length input = v input_len } ->
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
    Seq.equal (B.as_seq h1 dst) (Spec.Hash.PadFinish.finish a (B.as_seq h0 s))))

inline_for_extraction
let hash_st (a: hash_alg) =
  input:B.buffer uint8 ->
  input_len:size_t { B.length input = v input_len } ->
  dst:hash_t a ->
  ST.Stack unit
    (requires (fun h ->
      B.live h input /\
      B.live h dst /\
      B.disjoint input dst /\
      B.length input < max_input_length a))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (Spec.Hash.hash a (B.as_seq h0 input))))

