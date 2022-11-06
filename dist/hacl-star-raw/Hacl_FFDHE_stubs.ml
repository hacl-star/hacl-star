module CI = Cstubs_internals

external _1_Hacl_FFDHE_ffdhe_len : Unsigned.uint8 -> Unsigned.uint32
  = "_1_Hacl_FFDHE_ffdhe_len" 

external _2_Hacl_FFDHE_new_ffdhe_precomp_p : Unsigned.uint8 -> CI.voidp
  = "_2_Hacl_FFDHE_new_ffdhe_precomp_p" 

external _3_Hacl_FFDHE_ffdhe_secret_to_public_precomp
  : Unsigned.uint8 -> _ CI.fatptr -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_3_Hacl_FFDHE_ffdhe_secret_to_public_precomp" 

external _4_Hacl_FFDHE_ffdhe_secret_to_public
  : Unsigned.uint8 -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_4_Hacl_FFDHE_ffdhe_secret_to_public" 

external _5_Hacl_FFDHE_ffdhe_shared_secret_precomp
  : Unsigned.uint8 -> _ CI.fatptr -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint64
  = "_5_Hacl_FFDHE_ffdhe_shared_secret_precomp" 

external _6_Hacl_FFDHE_ffdhe_shared_secret
  : Unsigned.uint8 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    Unsigned.uint64 = "_6_Hacl_FFDHE_ffdhe_shared_secret" 

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
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x2; _},
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint64_t))))),
  "Hacl_FFDHE_ffdhe_shared_secret" ->
  (fun x1 x4 x5 x6 ->
    let x3 = x2 x1 in _6_Hacl_FFDHE_ffdhe_shared_secret x3 x4 x5 x6)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x8; _},
     Function
       (CI.Pointer _,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint64_t)))))),
  "Hacl_FFDHE_ffdhe_shared_secret_precomp" ->
  (fun x7 x10 x12 x13 x14 ->
    let CI.CPointer x11 = x10 in
    let x9 = x8 x7 in
    _5_Hacl_FFDHE_ffdhe_shared_secret_precomp x9 x11 x12 x13 x14)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x16; _},
     Function
       (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_FFDHE_ffdhe_secret_to_public" ->
  (fun x15 x18 x19 ->
    let x17 = x16 x15 in _4_Hacl_FFDHE_ffdhe_secret_to_public x17 x18 x19)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x21; _},
     Function
       (CI.Pointer _,
        Function
          (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_FFDHE_ffdhe_secret_to_public_precomp" ->
  (fun x20 x23 x25 x26 ->
    let CI.CPointer x24 = x23 in
    let x22 = x21 x20 in
    _3_Hacl_FFDHE_ffdhe_secret_to_public_precomp x22 x24 x25 x26)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x28; _},
     Returns (CI.Pointer x30)),
  "Hacl_FFDHE_new_ffdhe_precomp_p" ->
  (fun x27 ->
    let x29 = x28 x27 in
    CI.make_ptr x30 (_2_Hacl_FFDHE_new_ffdhe_precomp_p x29))
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x32; _},
     Returns (CI.Primitive CI.Uint32_t)),
  "Hacl_FFDHE_ffdhe_len" ->
  (fun x31 -> let x33 = x32 x31 in _1_Hacl_FFDHE_ffdhe_len x33)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
