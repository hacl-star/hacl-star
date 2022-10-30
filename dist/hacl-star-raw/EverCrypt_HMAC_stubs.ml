module CI = Cstubs_internals

external _1_EverCrypt_HMAC_compute_sha1
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_1_EverCrypt_HMAC_compute_sha1" 

external _2_EverCrypt_HMAC_compute_sha2_256
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_2_EverCrypt_HMAC_compute_sha2_256" 

external _3_EverCrypt_HMAC_compute_sha2_384
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_3_EverCrypt_HMAC_compute_sha2_384" 

external _4_EverCrypt_HMAC_compute_sha2_512
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_4_EverCrypt_HMAC_compute_sha2_512" 

external _5_EverCrypt_HMAC_compute_blake2s
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_5_EverCrypt_HMAC_compute_blake2s" 

external _6_EverCrypt_HMAC_compute_blake2b
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_6_EverCrypt_HMAC_compute_blake2b" 

external _7_EverCrypt_HMAC_is_supported_alg : Unsigned.uint8 -> bool
  = "_7_EverCrypt_HMAC_is_supported_alg" 

external _8_EverCrypt_HMAC_compute
  : Unsigned.uint8 -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_8_EverCrypt_HMAC_compute_byte6" "_8_EverCrypt_HMAC_compute" 

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
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.OCaml CI.Bytes,
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "EverCrypt_HMAC_compute" ->
  (fun x1 x4 x5 x6 x7 x8 ->
    let x3 = x2 x1 in _8_EverCrypt_HMAC_compute x3 x4 x5 x6 x7 x8)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x10; _},
     Returns (CI.Primitive CI.Bool)),
  "EverCrypt_HMAC_is_supported_alg" ->
  (fun x9 -> let x11 = x10 x9 in _7_EverCrypt_HMAC_is_supported_alg x11)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_blake2b" -> _6_EverCrypt_HMAC_compute_blake2b
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_blake2s" -> _5_EverCrypt_HMAC_compute_blake2s
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_sha2_512" -> _4_EverCrypt_HMAC_compute_sha2_512
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_sha2_384" -> _3_EverCrypt_HMAC_compute_sha2_384
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_sha2_256" -> _2_EverCrypt_HMAC_compute_sha2_256
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_sha1" -> _1_EverCrypt_HMAC_compute_sha1
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
