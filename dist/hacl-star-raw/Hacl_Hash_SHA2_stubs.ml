module CI = Cstubs_internals

external _1_Hacl_Hash_Core_SHA2_init_224 : _ CI.fatptr -> unit
  = "_1_Hacl_Hash_Core_SHA2_init_224" 

external _2_Hacl_Hash_Core_SHA2_init_256 : _ CI.fatptr -> unit
  = "_2_Hacl_Hash_Core_SHA2_init_256" 

external _3_Hacl_Hash_Core_SHA2_init_384 : _ CI.fatptr -> unit
  = "_3_Hacl_Hash_Core_SHA2_init_384" 

external _4_Hacl_Hash_Core_SHA2_init_512 : _ CI.fatptr -> unit
  = "_4_Hacl_Hash_Core_SHA2_init_512" 

external _5_Hacl_Hash_Core_SHA2_update_384
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_5_Hacl_Hash_Core_SHA2_update_384" 

external _6_Hacl_Hash_Core_SHA2_update_512
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_6_Hacl_Hash_Core_SHA2_update_512" 

external _7_Hacl_Hash_Core_SHA2_pad_256
  : Unsigned.uint64 -> bytes CI.ocaml -> unit
  = "_7_Hacl_Hash_Core_SHA2_pad_256" 

external _8_Hacl_Hash_Core_SHA2_finish_224
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_8_Hacl_Hash_Core_SHA2_finish_224" 

external _9_Hacl_Hash_Core_SHA2_finish_256
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_9_Hacl_Hash_Core_SHA2_finish_256" 

external _10_Hacl_Hash_Core_SHA2_finish_384
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_10_Hacl_Hash_Core_SHA2_finish_384" 

external _11_Hacl_Hash_Core_SHA2_finish_512
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_11_Hacl_Hash_Core_SHA2_finish_512" 

external _12_Hacl_Hash_SHA2_update_multi_224
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_12_Hacl_Hash_SHA2_update_multi_224" 

external _13_Hacl_Hash_SHA2_update_multi_256
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_13_Hacl_Hash_SHA2_update_multi_256" 

external _14_Hacl_Hash_SHA2_update_multi_384
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_14_Hacl_Hash_SHA2_update_multi_384" 

external _15_Hacl_Hash_SHA2_update_multi_512
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_15_Hacl_Hash_SHA2_update_multi_512" 

external _16_Hacl_Hash_SHA2_update_last_224
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> Unsigned.uint32 ->
    unit = "_16_Hacl_Hash_SHA2_update_last_224" 

external _17_Hacl_Hash_SHA2_update_last_256
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> Unsigned.uint32 ->
    unit = "_17_Hacl_Hash_SHA2_update_last_256" 

external _18_Hacl_Hash_SHA2_hash_224
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_18_Hacl_Hash_SHA2_hash_224" 

external _19_Hacl_Hash_SHA2_hash_256
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_19_Hacl_Hash_SHA2_hash_256" 

external _20_Hacl_Hash_SHA2_hash_384
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_20_Hacl_Hash_SHA2_hash_384" 

external _21_Hacl_Hash_SHA2_hash_512
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_21_Hacl_Hash_SHA2_hash_512" 

type 'a result = 'a
type 'a return = 'a
type 'a fn =
 | Returns  : 'a CI.typ   -> 'a return fn
 | Function : 'a CI.typ * 'b fn  -> ('a -> 'b) fn
let map_result f x = f x
let returning t = Returns t
let (@->) f p = Function (f, p)
let foreign : type a b. string -> (a -> b) fn -> (a -> b) =
  fun name t -> match t, name with
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Hash_SHA2_hash_512" -> _21_Hacl_Hash_SHA2_hash_512
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Hash_SHA2_hash_384" -> _20_Hacl_Hash_SHA2_hash_384
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Hash_SHA2_hash_256" -> _19_Hacl_Hash_SHA2_hash_256
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Hash_SHA2_hash_224" -> _18_Hacl_Hash_SHA2_hash_224
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))),
  "Hacl_Hash_SHA2_update_last_256" ->
  (fun x13 x15 x16 x17 ->
    let CI.CPointer x14 = x13 in
    _17_Hacl_Hash_SHA2_update_last_256 x14 x15 x16 x17)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))),
  "Hacl_Hash_SHA2_update_last_224" ->
  (fun x18 x20 x21 x22 ->
    let CI.CPointer x19 = x18 in
    _16_Hacl_Hash_SHA2_update_last_224 x19 x20 x21 x22)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Hash_SHA2_update_multi_512" ->
  (fun x23 x25 x26 ->
    let CI.CPointer x24 = x23 in
    _15_Hacl_Hash_SHA2_update_multi_512 x24 x25 x26)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Hash_SHA2_update_multi_384" ->
  (fun x27 x29 x30 ->
    let CI.CPointer x28 = x27 in
    _14_Hacl_Hash_SHA2_update_multi_384 x28 x29 x30)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Hash_SHA2_update_multi_256" ->
  (fun x31 x33 x34 ->
    let CI.CPointer x32 = x31 in
    _13_Hacl_Hash_SHA2_update_multi_256 x32 x33 x34)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Hash_SHA2_update_multi_224" ->
  (fun x35 x37 x38 ->
    let CI.CPointer x36 = x35 in
    _12_Hacl_Hash_SHA2_update_multi_224 x36 x37 x38)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_SHA2_finish_512" ->
  (fun x39 x41 ->
    let CI.CPointer x40 = x39 in _11_Hacl_Hash_Core_SHA2_finish_512 x40 x41)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_SHA2_finish_384" ->
  (fun x42 x44 ->
    let CI.CPointer x43 = x42 in _10_Hacl_Hash_Core_SHA2_finish_384 x43 x44)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_SHA2_finish_256" ->
  (fun x45 x47 ->
    let CI.CPointer x46 = x45 in _9_Hacl_Hash_Core_SHA2_finish_256 x46 x47)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_SHA2_finish_224" ->
  (fun x48 x50 ->
    let CI.CPointer x49 = x48 in _8_Hacl_Hash_Core_SHA2_finish_224 x49 x50)
| Function
    (CI.Primitive CI.Uint64_t, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_SHA2_pad_256" -> _7_Hacl_Hash_Core_SHA2_pad_256
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_SHA2_update_512" ->
  (fun x53 x55 ->
    let CI.CPointer x54 = x53 in _6_Hacl_Hash_Core_SHA2_update_512 x54 x55)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_SHA2_update_384" ->
  (fun x56 x58 ->
    let CI.CPointer x57 = x56 in _5_Hacl_Hash_Core_SHA2_update_384 x57 x58)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Hash_Core_SHA2_init_512" ->
  (fun x59 ->
    let CI.CPointer x60 = x59 in _4_Hacl_Hash_Core_SHA2_init_512 x60)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Hash_Core_SHA2_init_384" ->
  (fun x61 ->
    let CI.CPointer x62 = x61 in _3_Hacl_Hash_Core_SHA2_init_384 x62)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Hash_Core_SHA2_init_256" ->
  (fun x63 ->
    let CI.CPointer x64 = x63 in _2_Hacl_Hash_Core_SHA2_init_256 x64)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Hash_Core_SHA2_init_224" ->
  (fun x65 ->
    let CI.CPointer x66 = x65 in _1_Hacl_Hash_Core_SHA2_init_224 x66)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
