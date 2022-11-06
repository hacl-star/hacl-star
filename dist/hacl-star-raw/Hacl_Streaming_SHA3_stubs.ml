module CI = Cstubs_internals

external _1_Hacl_Streaming_SHA3_create_in_256 : unit -> CI.voidp
  = "_1_Hacl_Streaming_SHA3_create_in_256" 

external _2_Hacl_Streaming_SHA3_init_256 : _ CI.fatptr -> unit
  = "_2_Hacl_Streaming_SHA3_init_256" 

external _3_Hacl_Streaming_SHA3_update_256
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> Unsigned.uint32
  = "_3_Hacl_Streaming_SHA3_update_256" 

external _4_Hacl_Streaming_SHA3_finish_256
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_4_Hacl_Streaming_SHA3_finish_256" 

external _5_Hacl_Streaming_SHA3_free_256 : _ CI.fatptr -> unit
  = "_5_Hacl_Streaming_SHA3_free_256" 

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
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA3_free_256" ->
  (fun x1 -> let CI.CPointer x2 = x1 in _5_Hacl_Streaming_SHA3_free_256 x2)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Streaming_SHA3_finish_256" ->
  (fun x3 x5 ->
    let CI.CPointer x4 = x3 in _4_Hacl_Streaming_SHA3_finish_256 x4 x5)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_Streaming_SHA3_update_256" ->
  (fun x6 x8 x9 ->
    let CI.CPointer x7 = x6 in _3_Hacl_Streaming_SHA3_update_256 x7 x8 x9)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Streaming_SHA3_init_256" ->
  (fun x10 ->
    let CI.CPointer x11 = x10 in _2_Hacl_Streaming_SHA3_init_256 x11)
| Function (CI.Void, Returns (CI.Pointer x13)),
  "Hacl_Streaming_SHA3_create_in_256" ->
  (fun x12 -> CI.make_ptr x13 (_1_Hacl_Streaming_SHA3_create_in_256 x12))
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
