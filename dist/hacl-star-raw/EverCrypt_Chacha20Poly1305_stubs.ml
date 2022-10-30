module CI = Cstubs_internals

external _1_EverCrypt_Chacha20Poly1305_aead_encrypt
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    unit
  =
  "_1_EverCrypt_Chacha20Poly1305_aead_encrypt_byte8" "_1_EverCrypt_Chacha20Poly1305_aead_encrypt"
  

external _2_EverCrypt_Chacha20Poly1305_aead_decrypt
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    Unsigned.uint32
  =
  "_2_EverCrypt_Chacha20Poly1305_aead_decrypt_byte8" "_2_EverCrypt_Chacha20Poly1305_aead_decrypt"
  

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
                      (CI.OCaml CI.Bytes,
                       Function
                         (CI.OCaml CI.Bytes,
                          Returns (CI.Primitive CI.Uint32_t))))))))),
  "EverCrypt_Chacha20Poly1305_aead_decrypt" ->
  _2_EverCrypt_Chacha20Poly1305_aead_decrypt
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
                      (CI.OCaml CI.Bytes,
                       Function (CI.OCaml CI.Bytes, Returns CI.Void)))))))),
  "EverCrypt_Chacha20Poly1305_aead_encrypt" ->
  _1_EverCrypt_Chacha20Poly1305_aead_encrypt
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
