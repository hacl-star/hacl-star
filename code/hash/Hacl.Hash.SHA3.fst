module Hacl.Hash.SHA3

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST

friend Spec.Agile.Hash

let init_256 s =
  LowStar.Buffer.fill s (Lib.IntTypes.u64 0) 25ul

let update_multi_256: update_multi_st (| SHA3_256, () |) = fun s () blocks n_blocks ->
  // Lib.Buffer.loop_blocks (block_len SHA3_256) (n_blocks `FStar.UInt32.mul` block_len SHA3_256) blocks ...
  // Loops.repeati absorb_inner + proof that 
  admit ()

let update_last_256: update_last_st (| SHA3_256, () |) = fun s () input input_len ->
  let open Lib.IntTypes in
  if input_len = 136ul then begin
    Hacl.Impl.SHA3.absorb_inner 136ul input s;
    Hacl.Impl.SHA3.absorb_last (byte 0x06) 136ul 0ul (B.sub input input_len 0ul) s
  end else
    Hacl.Impl.SHA3.absorb_last (byte 0x06) 136ul input_len input s

let finish_256: finish_st (| SHA3_256, () |) = Hacl.Hash.PadFinish.finish (| SHA3_256, () |)
