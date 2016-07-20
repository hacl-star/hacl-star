module Hash.Sha256.Pure

open Hacl.UInt32
open Hacl.SBuffer


(* Define base types *)
let u32 = FStar.UInt32.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s


(* Define algorithm parameters *)
let hl = 32ul
let bl = 64ul
let hashsize = hl
let blocksize = bl


(* Define SHA2 functions *)
assume val init : unit -> Tot (state:uint32s)

assume val update : (state:uint32s) -> (data:bytes) -> (len:u32{length data = v len})
  -> Tot (state :uint32s)

assume val finish : (hash:bytes{length hash >= v hashsize}) -> (state:uint32s)
  -> Tot (Prims.tuple2 (hash:bytes{length hash >= v hashsize}) (state:uint32s))

assume val sha256 : (data:bytes) -> (len:u32{length data = v len})
  -> Tot (hash:bytes{length hash >= v hashsize})
