module CI = Cstubs_internals

external _1_Hacl_Impl_Chacha20_chacha20_init
  : _ CI.fatptr -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    unit = "_1_Hacl_Impl_Chacha20_chacha20_init" 

external _2_Hacl_Impl_Chacha20_chacha20_update
  : _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    unit = "_2_Hacl_Impl_Chacha20_chacha20_update" 

external _3_Hacl_Chacha20_chacha20_encrypt
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32 -> unit
  =
  "_3_Hacl_Chacha20_chacha20_encrypt_byte6" "_3_Hacl_Chacha20_chacha20_encrypt"
  

external _4_Hacl_Chacha20_chacha20_decrypt
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32 -> unit
  =
  "_4_Hacl_Chacha20_chacha20_decrypt_byte6" "_4_Hacl_Chacha20_chacha20_decrypt"
  

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
  "Hacl_Chacha20_chacha20_decrypt" -> _4_Hacl_Chacha20_chacha20_decrypt
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
  "Hacl_Chacha20_chacha20_encrypt" -> _3_Hacl_Chacha20_chacha20_encrypt
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_Impl_Chacha20_chacha20_update" ->
  (fun x13 x15 x16 x17 ->
    let CI.CPointer x14 = x13 in
    _2_Hacl_Impl_Chacha20_chacha20_update x14 x15 x16 x17)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))),
  "Hacl_Impl_Chacha20_chacha20_init" ->
  (fun x18 x20 x21 x22 ->
    let CI.CPointer x19 = x18 in
    _1_Hacl_Impl_Chacha20_chacha20_init x19 x20 x21 x22)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
