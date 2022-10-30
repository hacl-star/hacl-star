module CI = Cstubs_internals

external _1_EverCrypt_HKDF_expand_sha1
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> Unsigned.uint32 -> unit
  = "_1_EverCrypt_HKDF_expand_sha1_byte6" "_1_EverCrypt_HKDF_expand_sha1" 

external _2_EverCrypt_HKDF_extract_sha1
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_2_EverCrypt_HKDF_extract_sha1" 

external _3_EverCrypt_HKDF_expand_sha2_256
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> Unsigned.uint32 -> unit
  =
  "_3_EverCrypt_HKDF_expand_sha2_256_byte6" "_3_EverCrypt_HKDF_expand_sha2_256"
  

external _4_EverCrypt_HKDF_extract_sha2_256
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_4_EverCrypt_HKDF_extract_sha2_256" 

external _5_EverCrypt_HKDF_expand_sha2_384
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> Unsigned.uint32 -> unit
  =
  "_5_EverCrypt_HKDF_expand_sha2_384_byte6" "_5_EverCrypt_HKDF_expand_sha2_384"
  

external _6_EverCrypt_HKDF_extract_sha2_384
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_6_EverCrypt_HKDF_extract_sha2_384" 

external _7_EverCrypt_HKDF_expand_sha2_512
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> Unsigned.uint32 -> unit
  =
  "_7_EverCrypt_HKDF_expand_sha2_512_byte6" "_7_EverCrypt_HKDF_expand_sha2_512"
  

external _8_EverCrypt_HKDF_extract_sha2_512
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_8_EverCrypt_HKDF_extract_sha2_512" 

external _9_EverCrypt_HKDF_expand_blake2s
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> Unsigned.uint32 -> unit
  =
  "_9_EverCrypt_HKDF_expand_blake2s_byte6" "_9_EverCrypt_HKDF_expand_blake2s" 

external _10_EverCrypt_HKDF_extract_blake2s
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_10_EverCrypt_HKDF_extract_blake2s" 

external _11_EverCrypt_HKDF_expand_blake2b
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> Unsigned.uint32 -> unit
  =
  "_11_EverCrypt_HKDF_expand_blake2b_byte6" "_11_EverCrypt_HKDF_expand_blake2b"
  

external _12_EverCrypt_HKDF_extract_blake2b
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_12_EverCrypt_HKDF_extract_blake2b" 

external _13_EverCrypt_HKDF_expand
  : Unsigned.uint8 -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> Unsigned.uint32 -> Unsigned.uint32 -> unit
  = "_13_EverCrypt_HKDF_expand_byte7" "_13_EverCrypt_HKDF_expand" 

external _14_EverCrypt_HKDF_extract
  : Unsigned.uint8 -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_14_EverCrypt_HKDF_extract_byte6" "_14_EverCrypt_HKDF_extract" 

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
  "EverCrypt_HKDF_extract" ->
  (fun x1 x4 x5 x6 x7 x8 ->
    let x3 = x2 x1 in _14_EverCrypt_HKDF_extract x3 x4 x5 x6 x7 x8)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x10; _},
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.OCaml CI.Bytes,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))))),
  "EverCrypt_HKDF_expand" ->
  (fun x9 x12 x13 x14 x15 x16 x17 ->
    let x11 = x10 x9 in _13_EverCrypt_HKDF_expand x11 x12 x13 x14 x15 x16 x17)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HKDF_extract_blake2b" -> _12_EverCrypt_HKDF_extract_blake2b
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
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "EverCrypt_HKDF_expand_blake2b" -> _11_EverCrypt_HKDF_expand_blake2b
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HKDF_extract_blake2s" -> _10_EverCrypt_HKDF_extract_blake2s
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
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "EverCrypt_HKDF_expand_blake2s" -> _9_EverCrypt_HKDF_expand_blake2s
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HKDF_extract_sha2_512" -> _8_EverCrypt_HKDF_extract_sha2_512
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
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "EverCrypt_HKDF_expand_sha2_512" -> _7_EverCrypt_HKDF_expand_sha2_512
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HKDF_extract_sha2_384" -> _6_EverCrypt_HKDF_extract_sha2_384
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
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "EverCrypt_HKDF_expand_sha2_384" -> _5_EverCrypt_HKDF_expand_sha2_384
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HKDF_extract_sha2_256" -> _4_EverCrypt_HKDF_extract_sha2_256
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
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "EverCrypt_HKDF_expand_sha2_256" -> _3_EverCrypt_HKDF_expand_sha2_256
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HKDF_extract_sha1" -> _2_EverCrypt_HKDF_extract_sha1
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
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "EverCrypt_HKDF_expand_sha1" -> _1_EverCrypt_HKDF_expand_sha1
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
