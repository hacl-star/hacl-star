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

let absorb_inner_32 rateInBytes b s = Hacl.Impl.SHA3.Vec.absorb_inner
  #Hacl.Spec.SHA3.Vec.Common.M32 rateInBytes b s

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

// No longer inline_for_extraction noextract for code quality
// We need to expand the type because F* does not know that state i { is_keccak i }
// is the same as buffer uint64.
val init_ (a: keccak_alg): s:B.buffer Lib.IntTypes.uint64 { B.length s = 25 }
 -> FStar.HyperStack.ST.Stack unit
  (requires (fun h ->
    B.live h s))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer s) h0 h1) /\
    Hacl.Hash.Definitions.as_seq h1 s == Spec.Agile.Hash.init (get_alg (| a, () |))))

let init_ a s =
  [@inline_let] let s: s:B.buffer uint64 { B.length s = 25 } = s in
  LowStar.Buffer.fill s (Lib.IntTypes.u64 0) 25ul

let init a s = init_ a s

#pop-options

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
  let open Lib.NTuple in
  let open Lib.MultiBuffer in
  let open Hacl.Spec.SHA3.Vec.Common in
  let h0 = ST.get() in
  let l = block_len a *! n_blocks in
  Lib.IntVector.reveal_vec_1 U64;
  Hacl.Impl.SHA3.Vec.absorb_inner_nblocks #M32 absorb_inner_32 (block_len a) l (ntup1 blocks) s;
  Hacl.Spec.SHA3.Equiv.absorb_inner_repeat_blocks_multi_lemma (v (block_len a)) (v l)
    (as_seq_multi h0 (ntup1 blocks)) (B.as_seq h0 s)

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

#push-options "--z3rlimit 100"
let update_last_sha3 (a: keccak_alg): update_last_st_sha3 a = fun s () input input_len ->
  let open Lib.IntTypes in
  let open Lib.NTuple in
  let open Lib.MultiBuffer in
  let open Hacl.Spec.SHA3.Vec.Common in
  let suffix = if is_shake a then byte 0x1f else byte 0x06 in
  let len = block_len a in
  Lib.IntVector.reveal_vec_1 U64;
  assert (v len == rate a / 8);
  assert (v input_len <= v len);
  eq_lemma input_len len;
  assert ((input_len = len) == (v input_len = v len));
  if input_len = len then begin
    let h0 = ST.get() in
    assert (v input_len == v len);
    Hacl.Impl.SHA3.Vec.absorb_inner_block #M32 absorb_inner_32 len len (ntup1 input) 0ul s;
    Hacl.Spec.SHA3.Equiv.absorb_inner_block_r_lemma (v len)
      (as_seq_multi h0 (ntup1 input)) (B.as_seq h0 s);
    let h0' = ST.get() in
    Hacl.Impl.SHA3.Vec.absorb_final #M32 absorb_inner_32 len 0ul (ntup1 (B.sub input input_len 0ul)) suffix s;
    Hacl.Spec.SHA3.Equiv.absorb_last_r_lemma suffix (v len) 0
      (as_seq_multi #1 #0ul h0' (ntup1 (B.gsub input input_len 0ul))) (B.as_seq h0' s)
  end else begin
    let h0 = ST.get() in
    assert (v input_len < v len);
    Hacl.Impl.SHA3.Vec.absorb_final #M32 absorb_inner_32 len input_len (ntup1 input) suffix s;
    Hacl.Spec.SHA3.Equiv.absorb_last_r_lemma suffix (v len) (v input_len)
      (as_seq_multi h0 (ntup1 input)) (B.as_seq h0 s)
  end
#pop-options

let update_last = update_last_sha3

let finish a = Hacl.Hash.PadFinish.finish (| a, () |)

let hash a output input input_len =
  match a with
  | SHA3_224 -> Hacl.Hash.SHA3.Scalar.sha3_224 output input input_len
  | SHA3_256 -> Hacl.Hash.SHA3.Scalar.sha3_256 output input input_len
  | SHA3_384 -> Hacl.Hash.SHA3.Scalar.sha3_384 output input input_len
  | SHA3_512 -> Hacl.Hash.SHA3.Scalar.sha3_512 output input input_len

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.IntVector
open Lib.Buffer
open Lib.ByteBuffer
open Lib.NTuple
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
open Hacl.Impl.SHA3.Vec
open Hacl.Spec.SHA3.Equiv

module S = Spec.SHA3
module V = Hacl.Spec.SHA3.Vec

val squeeze: (let m = M32 in
     s:state_t m
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
    (requires fun h -> live_multi h b /\ live h s /\ internally_disjoint b /\
      disjoint_multi b s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s |+| loc_multi b) h0 h1 /\
      as_seq_multi h1 b == V.squeeze #m (as_seq h0 s) (v rateInBytes) (v
      outputByteLen) (as_seq_multi h0 b)))

let squeeze s rateInBytes outputByteLen b =
  squeeze #M32 s rateInBytes outputByteLen b

let finish_keccak (a: keccak_alg): finish_st a = fun s dst l ->
  let open Lib.NTuple in
  let open Lib.MultiBuffer in
  let open Hacl.Spec.SHA3.Vec.Common in
  Lib.IntVector.reveal_vec_1 U64;
  if is_shake a then begin
    let h0 = ST.get() in
    squeeze s (block_len a) l (ntup1 dst);
    Hacl.Spec.SHA3.Equiv.squeeze_s_lemma (B.as_seq h0 s) (v (block_len a))
      (v l) (as_seq_multi h0 (ntup1 dst))
  end else begin
    let h0 = ST.get() in
    squeeze s (block_len a) (hash_len a) (ntup1 dst);
    Hacl.Spec.SHA3.Equiv.squeeze_s_lemma (B.as_seq h0 s) (v (block_len a))
      (v (hash_len a)) (as_seq_multi h0 (ntup1 dst))
  end
