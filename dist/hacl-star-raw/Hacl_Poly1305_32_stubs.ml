module CI = Cstubs_internals

external _1_Hacl_Poly1305_32_poly1305_init
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_1_Hacl_Poly1305_32_poly1305_init" 

external _2_Hacl_Poly1305_32_poly1305_update1
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_2_Hacl_Poly1305_32_poly1305_update1" 

external _3_Hacl_Poly1305_32_poly1305_update
  : _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_3_Hacl_Poly1305_32_poly1305_update" 

external _4_Hacl_Poly1305_32_poly1305_finish
  : bytes CI.ocaml -> bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_4_Hacl_Poly1305_32_poly1305_finish" 

external _5_Hacl_Poly1305_32_poly1305_mac
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    unit = "_5_Hacl_Poly1305_32_poly1305_mac" 

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
        Function
          (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_Poly1305_32_poly1305_mac" -> _5_Hacl_Poly1305_32_poly1305_mac
| Function
    (CI.OCaml CI.Bytes,
     Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Poly1305_32_poly1305_finish" ->
  (fun x5 x6 x7 ->
    let CI.CPointer x8 = x7 in _4_Hacl_Poly1305_32_poly1305_finish x5 x6 x8)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Poly1305_32_poly1305_update" ->
  (fun x9 x11 x12 ->
    let CI.CPointer x10 = x9 in
    _3_Hacl_Poly1305_32_poly1305_update x10 x11 x12)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Poly1305_32_poly1305_update1" ->
  (fun x13 x15 ->
    let CI.CPointer x14 = x13 in _2_Hacl_Poly1305_32_poly1305_update1 x14 x15)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Poly1305_32_poly1305_init" ->
  (fun x16 x18 ->
    let CI.CPointer x17 = x16 in _1_Hacl_Poly1305_32_poly1305_init x17 x18)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
