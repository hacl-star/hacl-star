module CI = Cstubs_internals

external _1_Hacl_HMAC_legacy_compute_sha1
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_1_Hacl_HMAC_legacy_compute_sha1" 

external _2_Hacl_HMAC_compute_sha2_256
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_2_Hacl_HMAC_compute_sha2_256" 

external _3_Hacl_HMAC_compute_sha2_384
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_3_Hacl_HMAC_compute_sha2_384" 

external _4_Hacl_HMAC_compute_sha2_512
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_4_Hacl_HMAC_compute_sha2_512" 

external _5_Hacl_HMAC_compute_blake2s_32
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_5_Hacl_HMAC_compute_blake2s_32" 

external _6_Hacl_HMAC_compute_blake2b_32
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_6_Hacl_HMAC_compute_blake2b_32" 

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
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "Hacl_HMAC_compute_blake2b_32" -> _6_Hacl_HMAC_compute_blake2b_32
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "Hacl_HMAC_compute_blake2s_32" -> _5_Hacl_HMAC_compute_blake2s_32
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "Hacl_HMAC_compute_sha2_512" -> _4_Hacl_HMAC_compute_sha2_512
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "Hacl_HMAC_compute_sha2_384" -> _3_Hacl_HMAC_compute_sha2_384
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "Hacl_HMAC_compute_sha2_256" -> _2_Hacl_HMAC_compute_sha2_256
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "Hacl_HMAC_legacy_compute_sha1" -> _1_Hacl_HMAC_legacy_compute_sha1
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
