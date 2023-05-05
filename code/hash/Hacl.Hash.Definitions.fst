module Hacl.Hash.Definitions

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = LowStar.Modifies
module B = LowStar.Buffer
module Blake2 = Hacl.Impl.Blake2.Core

open Lib.IntTypes
open Spec.Hash.Definitions
open FStar.Mul

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

(** The low-level types that our clients need to be aware of, in order to
    successfully call this module. *)

inline_for_extraction noextract
let m_spec (a:hash_alg) : Type0 =
  match a with
  | Blake2S | Blake2B -> Blake2.m_spec
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> unit

inline_for_extraction noextract
let extra_state (a:hash_alg) : Type0 =
  match a with
  | Blake2S -> s:uint_t U64 PUB{ v s % block_length a = 0 }
  | Blake2B -> s:uint_t U128 PUB{ v s % block_length a = 0 }
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> unit

inline_for_extraction noextract
let ev_v (#a:hash_alg) (ev:extra_state a) : Spec.Hash.Definitions.extra_state a =
  match a with
  | Blake2S -> v #U64 #PUB ev
  | Blake2B -> v #U128 #PUB ev
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> ()

inline_for_extraction
type impl = a:hash_alg & m_spec a

inline_for_extraction noextract
let mk_impl (a:hash_alg) (m:m_spec a) : impl = (|a, m|)

inline_for_extraction noextract
let get_alg (i:impl) : hash_alg =
  match i with (|a, m|) -> a

inline_for_extraction noextract
let get_spec (i:impl) : m_spec (get_alg i) =
  match i with (|a, m|) -> m

inline_for_extraction noextract
let impl_word (i:impl) =
  [@inline_let] let a = get_alg i in
  match a with
  | Blake2S | Blake2B -> Blake2.element_t (to_blake_alg a) (get_spec i)
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> word a

inline_for_extraction noextract
let impl_state_length (i:impl) =
  [@inline_let] let a = get_alg i in
  match a with
  | Blake2S | Blake2B -> UInt32.v (4ul *. Blake2.row_len (to_blake_alg a) (get_spec i))
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> state_word_length a

inline_for_extraction noextract
let impl_state_len (i:impl) : s:size_t{size_v s == impl_state_length i} =
  [@inline_let] let a = get_alg i in
  [@inline_let] let m = get_spec i in
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> 8ul
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> 25ul
  | _ ->
    (**) mul_mod_lemma 4ul (Blake2.row_len (to_blake_alg a) (get_spec i));
    match a, m with
    | Blake2S, Blake2.M32
    | Blake2B, Blake2.M32 | Blake2B, Blake2.M128 -> 16ul
    | Blake2S, Blake2.M128 | Blake2S, Blake2.M256
    | Blake2B, Blake2.M256 -> 4ul

inline_for_extraction noextract
type state (i:impl) =
  b:B.buffer (impl_word i) { B.length b = impl_state_length i }

inline_for_extraction noextract
let as_seq (#i:impl) (h:HS.mem) (s:state i) : GTot (words_state (get_alg i)) =
  match get_alg i with
  | Blake2S -> Blake2.state_v #Spec.Blake2.Blake2S #(get_spec i) h s
  | Blake2B -> Blake2.state_v #Spec.Blake2.Blake2B #(get_spec i) h s
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> B.as_seq h s

inline_for_extraction
let word_len (a: md_alg) : n:size_t { v n = word_length a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 4ul
  | SHA2_384 | SHA2_512 -> 8ul

inline_for_extraction
let block_len (a: hash_alg): n:size_t { v n = block_length a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 64ul
  | SHA2_384 | SHA2_512 -> 128ul
  | SHA3_224 -> assert_norm (rate SHA3_224/8/8*8 = 144); 144ul
  | SHA3_256 -> assert_norm (rate SHA3_256/8/8*8 = 136); 136ul
  | SHA3_384 -> assert_norm (rate SHA3_384/8/8*8 = 104); 104ul
  | SHA3_512 -> assert_norm (rate SHA3_512/8/8*8 = 72); 72ul
  | Shake128 -> assert_norm (rate Shake128/8/8*8 = 168); 168ul
  | Shake256 -> assert_norm (rate Shake256/8/8*8 = 136); 136ul
  | Blake2S -> 64ul
  | Blake2B -> 128ul

inline_for_extraction
let hash_word_len (a: md_alg): n:size_t { v n = hash_word_length a } =
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 -> 7ul
  | SHA2_256 -> 8ul
  | SHA2_384 -> 6ul
  | SHA2_512 -> 8ul

inline_for_extraction
let hash_len (a: fixed_len_alg): n:size_t { v n = hash_length a } =
  match a with
  | MD5 -> 16ul
  | SHA1 -> 20ul
  | SHA2_224 -> 28ul
  | SHA2_256 -> 32ul
  | SHA2_384 -> 48ul
  | SHA2_512 -> 64ul
  | Blake2S -> 32ul
  | Blake2B -> 64ul
  | SHA3_224 -> 28ul
  | SHA3_256 -> 32ul
  | SHA3_384 -> 48ul
  | SHA3_512 -> 64ul

/// Maximum input length, but fitting on a 64-bit integer (since the streaming
/// module doesn't bother taking into account lengths that are greater than
/// that). The comment previously was:
///
/// Note that we keep the total length at run-time, on 64 bits, but require that
/// it abides by the size requirements for the smaller hashes -- we're not
/// interested at this stage in having an agile type for lengths that would be
/// up to 2^125 for SHA384/512.

module U64 = FStar.UInt64

inline_for_extraction noextract
let max_input_len64 a: U64.(x:t { 0 < v x /\ v x `less_than_max_input_length` a }) =
  let _ = allow_inversion hash_alg in
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 ->
      assert_norm (0 < pow2 61 - 1 && pow2 61 < pow2 64);
      normalize_term_spec (pow2 61 - 1);
      U64.uint_to_t (normalize_term (pow2 61 - 1))
  | SHA2_384 | SHA2_512 ->
      assert_norm (pow2 64 < pow2 125 - 1);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | Blake2S ->
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | Blake2B ->
      assert_norm (pow2 64 < pow2 128);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 ->
      // TODO: relax this?
      assert_norm (pow2 64 < pow2 128);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))

noextract inline_for_extraction
let blocks_t (a: hash_alg) =
  b:B.buffer uint8 { B.length b % block_length a = 0 }

let hash_t (a: fixed_len_alg) = b:B.buffer uint8 { B.length b = hash_length a }

(** The types of all stateful operations for a hash algorithm. *)

noextract inline_for_extraction
let alloca_st (i:impl) = unit -> ST.StackInline (state i)
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 s h1 ->
    M.(modifies M.loc_none h0 h1) /\
    B.frameOf s == HS.get_tip h0 /\
    as_seq h1 s == Spec.Agile.Hash.init (get_alg i) /\
    B.live h1 s /\
    B.fresh_loc (M.loc_buffer s) h0 h1))

noextract inline_for_extraction
let malloc_st (i:impl) = r:HS.rid -> ST.ST (state i)
  (requires (fun h ->
    ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    B.live h1 s /\
    M.(modifies M.loc_none h0 h1) /\
    B.fresh_loc (M.loc_addr_of_buffer s) h0 h1 /\
    M.(loc_includes (loc_region_only true r) (loc_addr_of_buffer s)) /\
    B.freeable s))

noextract inline_for_extraction
let init_st (i:impl) = s:state i -> ST.Stack unit
  (requires (fun h ->
    B.live h s))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer s) h0 h1) /\
    as_seq h1 s == Spec.Agile.Hash.init (get_alg i)))

noextract inline_for_extraction
let update_st (i:impl{is_md (get_alg i)}) =
  s:state i ->
  block:B.buffer uint8 { B.length block = block_length (get_alg i) } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h block /\ B.disjoint s block))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer s) h0 h1) /\
      as_seq h1 s ==
        Spec.Agile.Hash.update (get_alg i) (as_seq h0 s) (B.as_seq h0 block)))

noextract inline_for_extraction
let pad_st (a: md_alg) = len:len_t a -> dst:B.buffer uint8 ->
  ST.Stack unit
    (requires (fun h ->
      len_v a len `less_than_max_input_length` a /\
      B.live h dst /\
      B.length dst = pad_length a (len_v a len)))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (Spec.Hash.MD.pad a (len_v a len))))

// Note: we cannot take more than 4GB of data because we are currently
// constrained by the size of buffers...
noextract inline_for_extraction
let update_multi_st (i:impl) =
  s:state i ->
  ev:extra_state (get_alg i) ->
  blocks:blocks_t (get_alg i) ->
  n:size_t { B.length blocks = block_length (get_alg i) * v n } ->
  ST.Stack unit
    (requires (fun h ->
      Spec.Agile.Hash.update_multi_pre (get_alg i) (ev_v ev) (B.as_seq h blocks) /\
      B.live h s /\ B.live h blocks /\ B.disjoint s blocks))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      as_seq h1 s ==
        Spec.Agile.Hash.update_multi (get_alg i) (as_seq h0 s) (ev_v ev) (B.as_seq h0 blocks)))

noextract inline_for_extraction
let prev_len_t (a: hash_alg) =
  if is_keccak a then
    unit
  else
    prev_len:len_t a { len_v a prev_len % block_length a = 0 }

noextract inline_for_extraction
let prev_len_v #a (prev_len: prev_len_t a): Spec.Hash.Incremental.Definitions.prev_length_t a
=
  if is_keccak a then
    ()
  else
    len_v a prev_len

noextract inline_for_extraction
let extra_state_of_prev_length #a (x: Spec.Hash.Incremental.Definitions.prev_length_t a): Spec.Agile.Hash.extra_state a =
  match a with
  | Blake2B | Blake2S -> x
  | _ -> ()

noextract inline_for_extraction
let update_last_st (i:impl) =
  let a = get_alg i in
  s:state i ->
  prev_len:prev_len_t a ->
  input:B.buffer uint8 {
    (if is_keccak a then True else (B.length input + len_v a prev_len) `less_than_max_input_length` a) /\
    B.length input <= block_length a
  } ->
  input_len:size_t { B.length input = v input_len } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h input /\ B.disjoint s input /\
      Spec.Agile.Hash.update_multi_pre a (extra_state_of_prev_length (prev_len_v prev_len)) (B.as_seq h input)))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      as_seq h1 s ==
        Spec.Hash.Incremental.update_last a (as_seq h0 s)
                                          (prev_len_v prev_len)
                                          (B.as_seq h0 input)))

inline_for_extraction noextract
let fixed_len_impl = i:impl { not (is_shake (dfst i)) }

noextract inline_for_extraction
let finish_st (i:fixed_len_impl) =
  s:state i -> dst:hash_t (get_alg i) -> ST.Stack unit
  (requires (fun h ->
    B.live h s /\ B.live h dst /\ B.disjoint s dst))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst `loc_union` loc_buffer s) h0 h1) /\
    Seq.equal (B.as_seq h1 dst) (Spec.Agile.Hash.finish (get_alg i) (as_seq h0 s) ())))

noextract inline_for_extraction
let hash_st (a: fixed_len_alg) =
  input:B.buffer uint8 ->
  input_len:size_t { B.length input = v input_len } ->
  dst:hash_t a->
  ST.Stack unit
    (requires (fun h ->
      B.live h input /\
      B.live h dst /\
      B.disjoint input dst /\
      B.length input `less_than_max_input_length` a))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (Spec.Agile.Hash.hash a (B.as_seq h0 input))))
