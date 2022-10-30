module CI = Cstubs_internals

external _1_Hacl_Streaming_SHA2_create_in_224 : unit -> CI.voidp
  = "_1_Hacl_Streaming_SHA2_create_in_224" 

external _2_Hacl_Streaming_SHA2_init_224 : _ CI.fatptr -> unit
  = "_2_Hacl_Streaming_SHA2_init_224" 

external _3_Hacl_Streaming_SHA2_update_224
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_3_Hacl_Streaming_SHA2_update_224" 

external _4_Hacl_Streaming_SHA2_finish_224
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_4_Hacl_Streaming_SHA2_finish_224" 

external _5_Hacl_Streaming_SHA2_free_224 : _ CI.fatptr -> unit
  = "_5_Hacl_Streaming_SHA2_free_224" 

external _6_Hacl_Streaming_SHA2_create_in_256 : unit -> CI.voidp
  = "_6_Hacl_Streaming_SHA2_create_in_256" 

external _7_Hacl_Streaming_SHA2_init_256 : _ CI.fatptr -> unit
  = "_7_Hacl_Streaming_SHA2_init_256" 

external _8_Hacl_Streaming_SHA2_update_256
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_8_Hacl_Streaming_SHA2_update_256" 

external _9_Hacl_Streaming_SHA2_finish_256
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_9_Hacl_Streaming_SHA2_finish_256" 

external _10_Hacl_Streaming_SHA2_free_256 : _ CI.fatptr -> unit
  = "_10_Hacl_Streaming_SHA2_free_256" 

external _11_Hacl_Streaming_SHA2_create_in_384 : unit -> CI.voidp
  = "_11_Hacl_Streaming_SHA2_create_in_384" 

external _12_Hacl_Streaming_SHA2_init_384 : _ CI.fatptr -> unit
  = "_12_Hacl_Streaming_SHA2_init_384" 

external _13_Hacl_Streaming_SHA2_update_384
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_13_Hacl_Streaming_SHA2_update_384" 

external _14_Hacl_Streaming_SHA2_finish_384
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_14_Hacl_Streaming_SHA2_finish_384" 

external _15_Hacl_Streaming_SHA2_free_384 : _ CI.fatptr -> unit
  = "_15_Hacl_Streaming_SHA2_free_384" 

external _16_Hacl_Streaming_SHA2_create_in_512 : unit -> CI.voidp
  = "_16_Hacl_Streaming_SHA2_create_in_512" 

external _17_Hacl_Streaming_SHA2_init_512 : _ CI.fatptr -> unit
  = "_17_Hacl_Streaming_SHA2_init_512" 

external _18_Hacl_Streaming_SHA2_update_512
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_18_Hacl_Streaming_SHA2_update_512" 

external _19_Hacl_Streaming_SHA2_finish_512
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_19_Hacl_Streaming_SHA2_finish_512" 

external _20_Hacl_Streaming_SHA2_free_512 : _ CI.fatptr -> unit
  = "_20_Hacl_Streaming_SHA2_free_512" 

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
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA2_free_512" ->
  (fun x1 -> let CI.CPointer x2 = x1 in _20_Hacl_Streaming_SHA2_free_512 x2)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Streaming_SHA2_finish_512" ->
  (fun x3 x5 ->
    let CI.CPointer x4 = x3 in _19_Hacl_Streaming_SHA2_finish_512 x4 x5)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Streaming_SHA2_update_512" ->
  (fun x6 x8 x9 ->
    let CI.CPointer x7 = x6 in _18_Hacl_Streaming_SHA2_update_512 x7 x8 x9)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA2_init_512" ->
  (fun x10 ->
    let CI.CPointer x11 = x10 in _17_Hacl_Streaming_SHA2_init_512 x11)
| Function (CI.Void, Returns (CI.Pointer x13)),
  "Hacl_Streaming_SHA2_create_in_512" ->
  (fun x12 -> CI.make_ptr x13 (_16_Hacl_Streaming_SHA2_create_in_512 x12))
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA2_free_384" ->
  (fun x14 ->
    let CI.CPointer x15 = x14 in _15_Hacl_Streaming_SHA2_free_384 x15)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Streaming_SHA2_finish_384" ->
  (fun x16 x18 ->
    let CI.CPointer x17 = x16 in _14_Hacl_Streaming_SHA2_finish_384 x17 x18)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Streaming_SHA2_update_384" ->
  (fun x19 x21 x22 ->
    let CI.CPointer x20 = x19 in
    _13_Hacl_Streaming_SHA2_update_384 x20 x21 x22)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA2_init_384" ->
  (fun x23 ->
    let CI.CPointer x24 = x23 in _12_Hacl_Streaming_SHA2_init_384 x24)
| Function (CI.Void, Returns (CI.Pointer x26)),
  "Hacl_Streaming_SHA2_create_in_384" ->
  (fun x25 -> CI.make_ptr x26 (_11_Hacl_Streaming_SHA2_create_in_384 x25))
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA2_free_256" ->
  (fun x27 ->
    let CI.CPointer x28 = x27 in _10_Hacl_Streaming_SHA2_free_256 x28)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Streaming_SHA2_finish_256" ->
  (fun x29 x31 ->
    let CI.CPointer x30 = x29 in _9_Hacl_Streaming_SHA2_finish_256 x30 x31)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Streaming_SHA2_update_256" ->
  (fun x32 x34 x35 ->
    let CI.CPointer x33 = x32 in
    _8_Hacl_Streaming_SHA2_update_256 x33 x34 x35)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA2_init_256" ->
  (fun x36 ->
    let CI.CPointer x37 = x36 in _7_Hacl_Streaming_SHA2_init_256 x37)
| Function (CI.Void, Returns (CI.Pointer x39)),
  "Hacl_Streaming_SHA2_create_in_256" ->
  (fun x38 -> CI.make_ptr x39 (_6_Hacl_Streaming_SHA2_create_in_256 x38))
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA2_free_224" ->
  (fun x40 ->
    let CI.CPointer x41 = x40 in _5_Hacl_Streaming_SHA2_free_224 x41)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Streaming_SHA2_finish_224" ->
  (fun x42 x44 ->
    let CI.CPointer x43 = x42 in _4_Hacl_Streaming_SHA2_finish_224 x43 x44)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Streaming_SHA2_update_224" ->
  (fun x45 x47 x48 ->
    let CI.CPointer x46 = x45 in
    _3_Hacl_Streaming_SHA2_update_224 x46 x47 x48)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA2_init_224" ->
  (fun x49 ->
    let CI.CPointer x50 = x49 in _2_Hacl_Streaming_SHA2_init_224 x50)
| Function (CI.Void, Returns (CI.Pointer x52)),
  "Hacl_Streaming_SHA2_create_in_224" ->
  (fun x51 -> CI.make_ptr x52 (_1_Hacl_Streaming_SHA2_create_in_224 x51))
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
