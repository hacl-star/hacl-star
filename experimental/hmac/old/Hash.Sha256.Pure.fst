module Hash.Sha256.Pure

module I8 = FStar.UInt8
module I32 = FStar.UInt32
module I64 = FStar.UInt64
module IB = FStar.Buffer



(* Define base types *)
let i8 = FStar.UInt8.t
let i32 = FStar.UInt32.t
let buf32 = Seq.seq i32
let bytes = Seq.seq i8


(* Define algorithm parameters *)
let hashsize = 32ul
let blocksize = 64ul


(* Define SHA2 *)

//assume val init : unit -> Tot (state:buf32)
//assume val update : (state:buf32) -> (data:bytes) -> Tot (state :buf32)
//assume val finish : (state:buf32) -> Tot (Prims.tuple2 (hash:bytes{Seq.length hash = I32.v hashsize}) (state:buf32))

assume val sha256 : (data:bytes) -> Tot (hash:bytes{Seq.length hash = I32.v hashsize})
