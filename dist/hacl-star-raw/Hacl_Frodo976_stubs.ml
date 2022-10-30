module CI = Cstubs_internals

external _1_Hacl_Frodo976_crypto_bytes : unit -> CI.voidp
  = "_1_Hacl_Frodo976_crypto_bytes" 

external _2_Hacl_Frodo976_crypto_publickeybytes : unit -> CI.voidp
  = "_2_Hacl_Frodo976_crypto_publickeybytes" 

external _3_Hacl_Frodo976_crypto_secretkeybytes : unit -> CI.voidp
  = "_3_Hacl_Frodo976_crypto_secretkeybytes" 

external _4_Hacl_Frodo976_crypto_ciphertextbytes : unit -> CI.voidp
  = "_4_Hacl_Frodo976_crypto_ciphertextbytes" 

external _5_Hacl_Frodo976_crypto_kem_keypair
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  = "_5_Hacl_Frodo976_crypto_kem_keypair" 

external _6_Hacl_Frodo976_crypto_kem_enc
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  = "_6_Hacl_Frodo976_crypto_kem_enc" 

external _7_Hacl_Frodo976_crypto_kem_dec
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  = "_7_Hacl_Frodo976_crypto_kem_dec" 

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
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_Frodo976_crypto_kem_dec" -> _7_Hacl_Frodo976_crypto_kem_dec
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_Frodo976_crypto_kem_enc" -> _6_Hacl_Frodo976_crypto_kem_enc
| Function
    (CI.OCaml CI.Bytes,
     Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t))),
  "Hacl_Frodo976_crypto_kem_keypair" -> _5_Hacl_Frodo976_crypto_kem_keypair
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| (CI.Primitive CI.Uint32_t as x9), "Hacl_Frodo976_crypto_ciphertextbytes" ->
  (CI.make_ptr x9 (_4_Hacl_Frodo976_crypto_ciphertextbytes ()))
| (CI.Primitive CI.Uint32_t as x10), "Hacl_Frodo976_crypto_secretkeybytes" ->
  (CI.make_ptr x10 (_3_Hacl_Frodo976_crypto_secretkeybytes ()))
| (CI.Primitive CI.Uint32_t as x11), "Hacl_Frodo976_crypto_publickeybytes" ->
  (CI.make_ptr x11 (_2_Hacl_Frodo976_crypto_publickeybytes ()))
| (CI.Primitive CI.Uint32_t as x12), "Hacl_Frodo976_crypto_bytes" ->
  (CI.make_ptr x12 (_1_Hacl_Frodo976_crypto_bytes ()))
| _, s ->  Printf.ksprintf failwith "No match for %s" s
