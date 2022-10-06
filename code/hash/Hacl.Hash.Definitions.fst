module Hacl.Hash.Definitions

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = LowStar.Modifies
module B = LowStar.Buffer
module Spec = Spec.Hash.PadFinish
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
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 | SHA3_256 -> unit
  | Blake2S | Blake2B -> Blake2.m_spec

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
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 | SHA3_256 -> word a
  | Blake2S | Blake2B -> Blake2.element_t (to_blake_alg a) (get_spec i)

inline_for_extraction noextract
let impl_state_length (i:impl) =
  [@inline_let] let a = get_alg i in
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 | SHA3_256 -> state_word_length a
  | Blake2S | Blake2B -> UInt32.v (4ul *. Blake2.row_len (to_blake_alg a) (get_spec i))

inline_for_extraction noextract
let impl_state_len (i:impl) : s:size_t{size_v s == impl_state_length i} =
  [@inline_let] let a = get_alg i in
  [@inline_let] let m = get_spec i in
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> 8ul
  | SHA3_256 -> 25ul
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
let as_seq (#i:impl) (h:HS.mem) (s:state i) : GTot (words_state' (get_alg i)) =
  match get_alg i with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 | SHA3_256 -> B.as_seq h s
  | Blake2S -> Blake2.state_v #Spec.Blake2.Blake2S #(get_spec i) h s
  | Blake2B -> Blake2.state_v #Spec.Blake2.Blake2B #(get_spec i) h s

inline_for_extraction
let word_len (a: hash_alg) : n:size_t { v n = word_length a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 4ul
  | SHA2_384 | SHA2_512 | SHA3_256 -> 8ul
  | Blake2S -> 4ul
  | Blake2B -> 8ul

inline_for_extraction
let block_len (a: hash_alg): n:size_t { v n = block_length a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 64ul
  | SHA2_384 | SHA2_512 -> 128ul
  | SHA3_256 -> assert_norm (1088/8/8*8 = 136); 136ul
  | Blake2S -> 64ul
  | Blake2B -> 128ul

inline_for_extraction
let hash_word_len (a: hash_alg): n:size_t { v n = hash_word_length a } =
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 -> 7ul
  | SHA2_256 -> 8ul
  | SHA2_384 -> 6ul
  | SHA2_512 -> 8ul
  | SHA3_256 -> 4ul
  | Blake2S | Blake2B -> 8ul

inline_for_extraction
let hash_len (a: hash_alg): n:size_t { v n = hash_length a } =
  match a with
  | MD5 -> 16ul
  | SHA1 -> 20ul
  | SHA2_224 -> 28ul
  | SHA2_256 -> 32ul
  | SHA2_384 -> 48ul
  | SHA2_512 -> 64ul
  | SHA3_256 -> 32ul
  | Blake2S -> 32ul
  | Blake2B -> 64ul

noextract inline_for_extraction
let blocks_t (a: hash_alg) =
  b:B.buffer uint8 { B.length b % block_length a = 0 }

let hash_t (a: hash_alg) = b:B.buffer uint8 { B.length b = hash_length a }

// The proper way to generate an extra state from a constant nat.
noextract inline_for_extraction
let const_nat_to_extra_state (a:hash_alg{is_blake a}) (n:nat{n <= maxint U64}) :
  extra_state a =
  match a with
  | Blake2S -> mk_int #U64 #SEC n
  | Blake2B -> cast U128 SEC (mk_int #U64 #SEC n)

noextract inline_for_extraction
let initial_extra_state (a:hash_alg) : extra_state a =
  if is_blake a then const_nat_to_extra_state a 0
  else ()

(** The types of all stateful operations for a hash algorithm. *)

noextract inline_for_extraction
let alloca_st (i:impl) = unit -> ST.StackInline (state i & extra_state (get_alg i))
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 (s, v) h1 ->
    M.(modifies M.loc_none h0 h1) /\
    B.frameOf s == HS.get_tip h0 /\
    (as_seq h1 s, v) == Spec.Agile.Hash.init (get_alg i) /\
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
let init_st (i:impl) = s:state i -> ST.Stack (extra_state (get_alg i))
  (requires (fun h ->
    B.live h s))
  (ensures (fun h0 v h1 ->
    M.(modifies (loc_buffer s) h0 h1) /\
    (as_seq h1 s, v) == Spec.Agile.Hash.init (get_alg i)))

noextract inline_for_extraction
let update_st (i:impl) =
  s:state i ->
  v:extra_state (get_alg i) ->
  block:B.buffer uint8 { B.length block = block_length (get_alg i) } ->
  ST.Stack (extra_state (get_alg i))
    (requires (fun h ->
      B.live h s /\ B.live h block /\ B.disjoint s block))
    (ensures (fun h0 v' h1 ->
      M.(modifies (loc_buffer s) h0 h1) /\
      (as_seq h1 s, v') ==
        Spec.Agile.Hash.update (get_alg i) (as_seq h0 s, v) (B.as_seq h0 block)))

noextract inline_for_extraction
let pad_st (a: md_alg) = len:len_t a -> dst:B.buffer uint8 ->
  ST.Stack unit
    (requires (fun h ->
      len_v a len `less_than_max_input_length` a /\
      B.live h dst /\
      B.length dst = pad_length a (len_v a len)))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (Spec.pad a (len_v a len))))

// Note: we cannot take more than 4GB of data because we are currently
// constrained by the size of buffers...
noextract inline_for_extraction
let update_multi_st (i:impl) =
  s:state i ->
  ev:extra_state (get_alg i) ->
  blocks:blocks_t (get_alg i) ->
  n:size_t { B.length blocks = block_length (get_alg i) * v n } ->
  ST.Stack (extra_state (get_alg i))
    (requires (fun h ->
      B.live h s /\ B.live h blocks /\ B.disjoint s blocks))
    (ensures (fun h0 ev' h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      (as_seq h1 s, ev') ==
        Spec.Agile.Hash.update_multi (get_alg i) (as_seq h0 s, ev) (B.as_seq h0 blocks)))

noextract inline_for_extraction
let update_last_st (i:impl) =
  s:state i ->
  ev:extra_state (get_alg i) ->
  prev_len:len_t (get_alg i) { len_v (get_alg i) prev_len % block_length (get_alg i) = 0 } ->
  input:B.buffer uint8 { (B.length input + len_v (get_alg i) prev_len) `less_than_max_input_length` (get_alg i) /\ B.length input <= block_length (get_alg i) } ->
  input_len:size_t { B.length input = v input_len } ->
  ST.Stack (extra_state (get_alg i))
    (requires (fun h ->
      B.live h s /\ B.live h input /\ B.disjoint s input /\
      (* ``extra_state_v ev`` is equal to 0 if the algorithm is not blake *)
      (B.length input + extra_state_v ev) `less_than_max_input_length` (get_alg i)))
    (ensures (fun h0 ev' h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      (as_seq h1 s, ev') ==
        Spec.Hash.Incremental.update_last (get_alg i) (as_seq h0 s, ev)
                                          (len_v (get_alg i) prev_len)
                                          (B.as_seq h0 input)))

noextract inline_for_extraction
let finish_st (i:impl) =
  s:state i -> ev:extra_state (get_alg i) -> dst:hash_t (get_alg i) -> ST.Stack unit
  (requires (fun h ->
    B.live h s /\ B.live h dst /\ B.disjoint s dst))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst `loc_union` loc_buffer s) h0 h1) /\
    Seq.equal (B.as_seq h1 dst) (Spec.Hash.PadFinish.finish (get_alg i) (as_seq h0 s, ev))))

noextract inline_for_extraction
let hash_st (a: hash_alg) =
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
