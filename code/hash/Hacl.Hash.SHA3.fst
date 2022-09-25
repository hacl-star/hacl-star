module Hacl.Hash.SHA3

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST

friend Spec.Agile.Hash

let crucial_fact = Spec.Hash.Incremental.sha3_state_is_hash_state

let init_256 s =
  LowStar.Buffer.fill s (Lib.IntTypes.u64 0) 25ul

inline_for_extraction noextract
let update_256: update_st (| SHA3_256, () |) = fun s () b ->
  Hacl.Impl.SHA3.absorb_inner 136ul b s

let update_multi_256: update_multi_st (| SHA3_256, () |) = Hacl.Hash.MD.mk_update_multi SHA3_256 update_256

let update_last_256: update_last_st (| SHA3_256, () |) = fun s () () input input_len ->
  let open Lib.IntTypes in
  if input_len = 136ul then begin
    Hacl.Impl.SHA3.absorb_inner 136ul input s;
    Hacl.Impl.SHA3.absorb_last (byte 0x06) 136ul 0ul (B.null #Lib.IntTypes.uint8) s
  end else
    Hacl.Impl.SHA3.absorb_last (byte 0x06) 136ul input_len input s

let finish_256: finish_st (| SHA3_256, () |) = Hacl.Hash.PadFinish.finish (| SHA3_256, () |)
