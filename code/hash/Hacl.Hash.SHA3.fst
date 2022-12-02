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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let spec_l (inpLen:size_t) (len:size_nat{len == v inpLen % block_length SHA3_256}) (inp:Lib.Sequence.lseq uint8 len) (s:Lib.Sequence.lseq uint64 25) = s


let aux (s:words_state SHA3_256) : Lemma (Lib.Sequence.repeat_blocks (block_length SHA3_256) S.empty (Spec.SHA3.absorb_inner (1088/8)) (spec_l 0ul) s == s)
  = admit()


// let last_noop (inpLen:Lib.IntTypes.size_t) (len:Lib.IntTypes.size_t{Lib.IntTypes.v len == Lib.IntTypes.v inpLen % block_length SHA3_256})
//   (inp:Lib.Buffer.lbuffer Lib.IntTypes.uint8 len)
//   (s:state (| SHA3_256, () |))
//   = s

let update_multi_256: update_multi_st (| SHA3_256, () |) = fun s () blocks n_blocks ->
  let h0 = ST.get () in
  [@inline_let]
  let blocks_len:size_t = n_blocks `FStar.UInt32.mul` block_len SHA3_256 in
  assert_norm (v 136ul == 1088/8);
  assert (v (block_len SHA3_256) == block_length SHA3_256);
  Lib.Buffer.loop_blocks #uint8 #uint64 (block_len SHA3_256) blocks_len blocks (Spec.SHA3.absorb_inner (1088/8)) (spec_l blocks_len) (Hacl.Impl.SHA3.absorb_inner 136ul) (fun _ _ _ -> ()) s;
  let h1 = ST.get () in
  assert (B.as_seq h1 s == Lib.Sequence.repeat_blocks #uint8 #(Lib.Sequence.lseq uint64 25) (block_length SHA3_256) (B.as_seq h0 blocks) (Spec.SHA3.absorb_inner (1088/8)) (spec_l blocks_len) (B.as_seq h0 s));
  assume (B.as_seq h1 s ==
    Lib.Sequence.repeat_blocks (block_length SHA3_256) S.empty (Spec.SHA3.absorb_inner (1088/8)) (spec_l blocks_len)
       (Lib.Sequence.repeat_blocks_multi (block_length SHA3_256) (B.as_seq h0 blocks) (Spec.SHA3.absorb_inner (1088/8)) (B.as_seq h0 s)));
  aux (Lib.Sequence.repeat_blocks_multi (block_length SHA3_256)  (B.as_seq h0 blocks) (Spec.SHA3.absorb_inner (1088/8)) (B.as_seq h0 s));
  admit()


  // Lib.Sequence.Lemmas.repeat_blocks_split (block_length SHA3_256) (B.length blocks) (B.as_seq h0 blocks) (Spec.SHA3.absorb_inner (1088/8)) (spec_l blocks_len) (B.as_seq h0 s);



  // Loops.repeati absorb_inner + proof that
  //admit ()

let update_last_256: update_last_st (| SHA3_256, () |) = fun s () input input_len ->
  let open Lib.IntTypes in
  if input_len = 136ul then begin
    Hacl.Impl.SHA3.absorb_inner 136ul input s;
    Hacl.Impl.SHA3.absorb_last (byte 0x06) 136ul 0ul (B.sub input input_len 0ul) s
  end else
    Hacl.Impl.SHA3.absorb_last (byte 0x06) 136ul input_len input s

let finish_256: finish_st (| SHA3_256, () |) = Hacl.Hash.PadFinish.finish (| SHA3_256, () |)
