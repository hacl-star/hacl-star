module Hacl.Hash.SHA3

open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open FStar.Mul

module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
open Lib.IntTypes

module LB = Lib.Buffer

friend Spec.Agile.Hash

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// We name this function used in Lib.Sequence spec combinators to avoid Z3 reasoning on anonymous functions
inline_for_extraction noextract
let spec_l (a: keccak_alg)
  (len:size_nat{len < block_length a})
  (inp:Lib.Sequence.lseq uint8 len)
  (s:Lib.Sequence.lseq uint64 25) = s

// TODO: for some reason, doing `let block_len = block_len` still results in excessive inlining.
let block_len (a: keccak_alg): n:size_t { v n = block_length a } =
  let open Spec.Hash.Definitions in
  let open FStar.Mul in
  [@inline_let]
  let _ = allow_inversion hash_alg in
  match a with
  | SHA3_224 -> assert_norm (rate SHA3_224/8/8*8 = 144); 144ul
  | SHA3_256 -> assert_norm (rate SHA3_256/8/8*8 = 136); 136ul
  | SHA3_384 -> assert_norm (rate SHA3_384/8/8*8 = 104); 104ul
  | SHA3_512 -> assert_norm (rate SHA3_512/8/8*8 = 72); 72ul
  | Shake128 -> assert_norm (rate Shake128/8/8*8 = 168); 168ul
  | Shake256 -> assert_norm (rate Shake256/8/8*8 = 136); 136ul

let hash_len (a: keccak_alg { not (is_shake a) }): Lib.IntTypes.(n:size_t { v n = hash_length a }) =
  match a with
  | SHA3_224 -> 28ul
  | SHA3_256 -> 32ul
  | SHA3_384 -> 48ul
  | SHA3_512 -> 64ul

let init a s =
  [@inline_let] let s: s:B.buffer uint64 { B.length s = 25 } = s in
  LowStar.Buffer.fill s (Lib.IntTypes.u64 0) 25ul

noextract inline_for_extraction
let is_shake a = a = Shake128 || a = Shake256

noextract inline_for_extraction
let update_multi_sha3_st (a:keccak_alg) =
  s:B.buffer uint64 { B.length s = 25 } ->
  ev:unit ->
  blocks:blocks_t a ->
  n:size_t { B.length blocks = block_length a * v n } ->
  ST.Stack unit
    (requires (fun h ->
      Spec.Agile.Hash.update_multi_pre a () (B.as_seq h blocks) /\
      B.live h s /\ B.live h blocks /\ B.disjoint s blocks))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      B.as_seq h1 s ==
        Spec.Agile.Hash.update_multi a (B.as_seq h0 s) () (B.as_seq h0 blocks)))

/// This function needs to be type-checked monomorphically (not with agile
/// types) so as to extract to Low* as-is.
let update_multi_sha3 (a: keccak_alg): update_multi_sha3_st a = fun s () blocks n_blocks ->
  [@inline_let]
  let spec_f = Spec.SHA3.absorb_inner (Spec.Hash.Definitions.rate a/8) in
  let h0 = ST.get () in
  Lib.Buffer.loop_blocks_multi (block_len a) n_blocks blocks spec_f (Hacl.Impl.SHA3.absorb_inner (block_len a)) s

/// There is a proof going here, that if your algorithm is of the keccak family,
/// then the monomorphic, Low*-compatible signature above, is a refinement of
/// the agile signature exported in the fsti. Thanks to the
/// inline_for_extraction on update_multi in the fsti, all that krml sees is the
/// monomorphic version. (The agile version does not extract.)
let update_multi = update_multi_sha3

noextract inline_for_extraction
let update_last_st_sha3 (a: keccak_alg) =
  s:B.buffer uint64 { B.length s = 25 } ->
  prev_len:unit ->
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
      B.as_seq h1 s ==
        Spec.Hash.Incremental.update_last a (B.as_seq h0 s)
                                          (prev_len_v prev_len)
                                          (B.as_seq h0 input)))

let update_last_sha3 (a: keccak_alg): update_last_st_sha3 a = fun s () input input_len ->
  let open Lib.IntTypes in
  let suffix = if is_shake a then byte 0x1f else byte 0x06 in
  let len = block_len a in
  if input_len = len then begin
    Hacl.Impl.SHA3.absorb_inner len input s;
    Hacl.Impl.SHA3.absorb_last suffix len 0ul (B.sub input input_len 0ul) s
  end else
    Hacl.Impl.SHA3.absorb_last suffix len input_len input s

let update_last = update_last_sha3

let finish a = Hacl.Hash.PadFinish.finish (| a, () |)

let hash a input len dst =
  match a with
  | SHA3_224 -> Hacl.SHA3.sha3_224 len input dst
  | SHA3_256 -> Hacl.SHA3.sha3_256 len input dst
  | SHA3_384 -> Hacl.SHA3.sha3_384 len input dst
  | SHA3_512 -> Hacl.SHA3.sha3_512 len input dst

let finish_keccak (a: keccak_alg): finish_st a = fun s dst l ->
  if is_shake a then
    Hacl.Impl.SHA3.squeeze s (block_len a) l dst
  else
    Hacl.Impl.SHA3.squeeze s (block_len a) (hash_len a) dst
