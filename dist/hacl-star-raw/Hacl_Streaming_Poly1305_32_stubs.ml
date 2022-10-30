module CI = Cstubs_internals

external _1_Hacl_Streaming_Poly1305_32_create_in : bytes CI.ocaml -> CI.voidp
  = "_1_Hacl_Streaming_Poly1305_32_create_in" 

external _2_Hacl_Streaming_Poly1305_32_init
  : bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_2_Hacl_Streaming_Poly1305_32_init" 

external _3_Hacl_Streaming_Poly1305_32_update
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_3_Hacl_Streaming_Poly1305_32_update" 

external _4_Hacl_Streaming_Poly1305_32_finish
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_4_Hacl_Streaming_Poly1305_32_finish" 

external _5_Hacl_Streaming_Poly1305_32_free : _ CI.fatptr -> unit
  = "_5_Hacl_Streaming_Poly1305_32_free" 

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
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_Poly1305_32_free" ->
  (fun x1 ->
    let CI.CPointer x2 = x1 in _5_Hacl_Streaming_Poly1305_32_free x2)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Streaming_Poly1305_32_finish" ->
  (fun x3 x5 ->
    let CI.CPointer x4 = x3 in _4_Hacl_Streaming_Poly1305_32_finish x4 x5)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Streaming_Poly1305_32_update" ->
  (fun x6 x8 x9 ->
    let CI.CPointer x7 = x6 in _3_Hacl_Streaming_Poly1305_32_update x7 x8 x9)
| Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Streaming_Poly1305_32_init" ->
  (fun x10 x11 ->
    let CI.CPointer x12 = x11 in _2_Hacl_Streaming_Poly1305_32_init x10 x12)
| Function (CI.OCaml CI.Bytes, Returns (CI.Pointer x14)),
  "Hacl_Streaming_Poly1305_32_create_in" ->
  (fun x13 -> CI.make_ptr x14 (_1_Hacl_Streaming_Poly1305_32_create_in x13))
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
