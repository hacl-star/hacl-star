open Ctypes
open PosixTypes
open Foreign

let uint8_ptr buf = from_voidp uint8_t (to_voidp (bigarray_start array1 buf))
let uint64_ptr buf = from_voidp uint64_t (to_voidp (bigarray_start array1 buf))

let size_uint32 buf = Unsigned.UInt32.of_int (Bigstring.size buf)
