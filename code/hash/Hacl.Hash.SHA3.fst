module Hacl.Hash.SHA3

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
open Lib.IntTypes

module LB = Lib.Buffer

friend Spec.Agile.Hash

let init_256 s =
  LowStar.Buffer.fill s (Lib.IntTypes.u64 0) 25ul

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// We name this function used in Lib.Sequence spec combinators to avoid Z3 reasoning on anonymous functions
inline_for_extraction noextract
let spec_l (len:size_nat{len < block_length SHA3_256}) (inp:Lib.Sequence.lseq uint8 len) (s:Lib.Sequence.lseq uint64 25) = s

let update_multi_256: update_multi_st (| SHA3_256, () |) = fun s () blocks n_blocks ->
  [@inline_let]
  let spec_f = Spec.SHA3.absorb_inner (1088/8) in
  let h0 = ST.get () in
  Lib.Buffer.loop_blocks (block_len SHA3_256) n_blocks 0ul blocks spec_f spec_l (Hacl.Impl.SHA3.absorb_inner 136ul) (fun _ _ _ -> ()) s;
  let open Lib.Sequence in
  calc (==) {
    repeat_blocks (block_length SHA3_256) (B.as_seq h0 blocks) spec_f spec_l (as_seq h0 s);
    (==) {   Lib.Sequence.Lemmas.lemma_repeat_blocks_via_multi (block_length SHA3_256) (B.as_seq h0 blocks) spec_f spec_l (as_seq h0 s) }
    spec_l 0 S.empty (repeat_blocks_multi (block_length SHA3_256) (B.as_seq h0 blocks) spec_f (as_seq h0 s));
    (==) { }
    repeat_blocks_multi (block_length SHA3_256) (B.as_seq h0 blocks) spec_f (as_seq h0 s);
  }

let update_last_256: update_last_st (| SHA3_256, () |) = fun s () input input_len ->
  let open Lib.IntTypes in
  if input_len = 136ul then begin
    Hacl.Impl.SHA3.absorb_inner 136ul input s;
    Hacl.Impl.SHA3.absorb_last (byte 0x06) 136ul 0ul (B.sub input input_len 0ul) s
  end else
    Hacl.Impl.SHA3.absorb_last (byte 0x06) 136ul input_len input s

let finish_256: finish_st (| SHA3_256, () |) = Hacl.Hash.PadFinish.finish (| SHA3_256, () |)

let hash_256: hash_st SHA3_256 = fun input len dst -> Hacl.SHA3.sha3_256 len input dst
