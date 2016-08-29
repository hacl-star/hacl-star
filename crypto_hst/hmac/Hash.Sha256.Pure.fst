module Hash.Sha256.Pure

module U8 = FStar.UInt8
module S8 = Hacl.UInt8
module U32 = FStar.UInt32
module S32 = Hacl.UInt32
module U64 = FStar.UInt64
module S64 = Hacl.UInt64
module SB = Hacl.SBuffer


(* Define base types *)
let u8 = FStar.UInt8.t
let s8 = Hacl.UInt8.t
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t
let uint32s = Seq.seq s32
let bytes = Seq.seq s8


(* Define algorithm parameters *)
let hl = 32ul
let bl = 64ul
let hashsize = hl
let blocksize = bl


(* Define SHA2 functions *)

assume val init : unit -> Tot (state:uint32s)

assume val update : (state:uint32s) -> (data:bytes) -> (len:s32{Seq.length data = S32.v len})
  -> Tot (state :uint32s)

assume val finish : (state:uint32s)
  -> Tot (Prims.tuple2 (hash:bytes{Seq.length hash = U32.v hashsize}) (state:uint32s))

assume val sha256 : (data:bytes) -> (len:s32{Seq.length data = S32.v len})
  -> Tot (hash:bytes{Seq.length hash = U32.v hashsize})
