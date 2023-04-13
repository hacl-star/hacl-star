module Hacl.Hash.SHA3

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
open Lib.IntTypes

module LB = Lib.Buffer

friend Spec.Agile.Hash

let init a s =
  LowStar.Buffer.fill s (Lib.IntTypes.u64 0) 25ul

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// We name this function used in Lib.Sequence spec combinators to avoid Z3 reasoning on anonymous functions
inline_for_extraction noextract
let spec_l (a: sha3_alg { not (is_shake a) })
  (len:size_nat{len < block_length a})
  (inp:Lib.Sequence.lseq uint8 len)
  (s:Lib.Sequence.lseq uint64 25) = s

let update_multi a s () blocks n_blocks =
  [@inline_let]
  let spec_f = Spec.SHA3.absorb_inner (Spec.Hash.Definitions.rate a/8) in
  let h0 = ST.get () in
  Lib.Buffer.loop_blocks (block_len a) n_blocks 0ul blocks spec_f (spec_l a) (Hacl.Impl.SHA3.absorb_inner (Hacl.Hash.Definitions.block_len a)) (fun _ _ _ -> ()) s;
  let open Lib.Sequence in
  calc (==) {
    repeat_blocks (block_length a) (B.as_seq h0 blocks) spec_f (spec_l a) (as_seq h0 s);
    (==) {   Lib.Sequence.Lemmas.lemma_repeat_blocks_via_multi (block_length a) (B.as_seq h0 blocks) spec_f (spec_l a) (as_seq h0 s) }
    (spec_l a) 0 S.empty (repeat_blocks_multi (block_length a) (B.as_seq h0 blocks) spec_f (as_seq h0 s));
    (==) { }
    repeat_blocks_multi (block_length a) (B.as_seq h0 blocks) spec_f (as_seq h0 s);
  }

let update_last a s () input input_len =
  let open Lib.IntTypes in
  if input_len = block_len a then begin
    Hacl.Impl.SHA3.absorb_inner (block_len a) input s;
    Hacl.Impl.SHA3.absorb_last (byte 0x06) (block_len a) 0ul (B.sub input input_len 0ul) s
  end else
    Hacl.Impl.SHA3.absorb_last (byte 0x06) (block_len a) input_len input s

let finish a = Hacl.Hash.PadFinish.finish (| a, () |)

let hash a input len dst =
  match a with
  | SHA3_224 -> Hacl.SHA3.sha3_224 len input dst
  | SHA3_256 -> Hacl.SHA3.sha3_256 len input dst
  | SHA3_384 -> Hacl.SHA3.sha3_384 len input dst
  | SHA3_512 -> Hacl.SHA3.sha3_512 len input dst

let finish_keccak (a: sha3_alg): finish_st a = fun s dst l ->
  if is_shake a then
    Hacl.Impl.SHA3.squeeze s (block_len a) l dst
  else
    Hacl.Impl.SHA3.squeeze s (block_len a) (hash_len a) dst
