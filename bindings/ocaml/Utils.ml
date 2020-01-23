open Ctypes
open PosixTypes
open Foreign

let uint8_ptr_of_bigstring buf = from_voidp uint8_t (to_voidp (bigarray_start array1 buf))
