module CI = Cstubs_internals

external _1_Hacl_HPKE_Curve51_CP256_SHA256_setupBaseS
  : bytes CI.ocaml -> _ CI.fatptr -> bytes CI.ocaml -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32
  =
  "_1_Hacl_HPKE_Curve51_CP256_SHA256_setupBaseS_byte6" "_1_Hacl_HPKE_Curve51_CP256_SHA256_setupBaseS"
  

external _2_Hacl_HPKE_Curve51_CP256_SHA256_setupBaseR
  : _ CI.fatptr -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> Unsigned.uint32
  = "_2_Hacl_HPKE_Curve51_CP256_SHA256_setupBaseR" 

external _3_Hacl_HPKE_Curve51_CP256_SHA256_sealBase
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  =
  "_3_Hacl_HPKE_Curve51_CP256_SHA256_sealBase_byte10" "_3_Hacl_HPKE_Curve51_CP256_SHA256_sealBase"
  

external _4_Hacl_HPKE_Curve51_CP256_SHA256_openBase
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32
  =
  "_4_Hacl_HPKE_Curve51_CP256_SHA256_openBase_byte9" "_4_Hacl_HPKE_Curve51_CP256_SHA256_openBase"
  

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
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.OCaml CI.Bytes,
                    Function
                      (CI.Primitive CI.Uint32_t,
                       Function
                         (CI.OCaml CI.Bytes,
                          Function
                            (CI.OCaml CI.Bytes,
                             Returns (CI.Primitive CI.Uint32_t)))))))))),
  "Hacl_HPKE_Curve51_CP256_SHA256_openBase" ->
  _4_Hacl_HPKE_Curve51_CP256_SHA256_openBase
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.OCaml CI.Bytes,
                    Function
                      (CI.Primitive CI.Uint32_t,
                       Function
                         (CI.OCaml CI.Bytes,
                          Function
                            (CI.OCaml CI.Bytes,
                             Function
                               (CI.OCaml CI.Bytes,
                                Returns (CI.Primitive CI.Uint32_t))))))))))),
  "Hacl_HPKE_Curve51_CP256_SHA256_sealBase" ->
  _3_Hacl_HPKE_Curve51_CP256_SHA256_sealBase
| Function
    (CI.Struct _,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_HPKE_Curve51_CP256_SHA256_setupBaseR" ->
  (fun x20 x22 x23 x24 x25 ->
    let CI.CPointer x21 = Ctypes.addr x20 in
    _2_Hacl_HPKE_Curve51_CP256_SHA256_setupBaseR x21 x22 x23 x24 x25)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Struct _,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_HPKE_Curve51_CP256_SHA256_setupBaseS" ->
  (fun x26 x27 x29 x30 x31 x32 ->
    let CI.CPointer x28 = Ctypes.addr x27 in
    _1_Hacl_HPKE_Curve51_CP256_SHA256_setupBaseS x26 x28 x29 x30 x31 x32)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
