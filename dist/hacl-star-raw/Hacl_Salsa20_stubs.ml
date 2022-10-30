module CI = Cstubs_internals

external _1_Hacl_Salsa20_salsa20_encrypt
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_1_Hacl_Salsa20_salsa20_encrypt_byte6" "_1_Hacl_Salsa20_salsa20_encrypt" 

external _2_Hacl_Salsa20_salsa20_decrypt
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_2_Hacl_Salsa20_salsa20_decrypt_byte6" "_2_Hacl_Salsa20_salsa20_decrypt" 

external _3_Hacl_Salsa20_salsa20_key_block0
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_3_Hacl_Salsa20_salsa20_key_block0" 

external _4_Hacl_Salsa20_hsalsa20
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_4_Hacl_Salsa20_hsalsa20" 

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
       (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Salsa20_hsalsa20" -> _4_Hacl_Salsa20_hsalsa20
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Salsa20_salsa20_key_block0" -> _3_Hacl_Salsa20_salsa20_key_block0
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes,
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "Hacl_Salsa20_salsa20_decrypt" -> _2_Hacl_Salsa20_salsa20_decrypt
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes,
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "Hacl_Salsa20_salsa20_encrypt" -> _1_Hacl_Salsa20_salsa20_encrypt
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
