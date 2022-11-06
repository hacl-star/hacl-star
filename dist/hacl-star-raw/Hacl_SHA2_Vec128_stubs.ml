module CI = Cstubs_internals

external _1_Hacl_SHA2_Vec128_sha224_4
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> unit
  = "_1_Hacl_SHA2_Vec128_sha224_4_byte9" "_1_Hacl_SHA2_Vec128_sha224_4" 

external _2_Hacl_SHA2_Vec128_sha256_4
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> unit
  = "_2_Hacl_SHA2_Vec128_sha256_4_byte9" "_2_Hacl_SHA2_Vec128_sha256_4" 

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
          (CI.OCaml CI.Bytes,
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
                          Function (CI.OCaml CI.Bytes, Returns CI.Void))))))))),
  "Hacl_SHA2_Vec128_sha256_4" -> _2_Hacl_SHA2_Vec128_sha256_4
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
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
                          Function (CI.OCaml CI.Bytes, Returns CI.Void))))))))),
  "Hacl_SHA2_Vec128_sha224_4" -> _1_Hacl_SHA2_Vec128_sha224_4
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
