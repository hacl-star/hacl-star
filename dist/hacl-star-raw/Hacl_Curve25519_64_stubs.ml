module CI = Cstubs_internals

external _1_Hacl_Curve25519_64_scalarmult
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_1_Hacl_Curve25519_64_scalarmult" 

external _2_Hacl_Curve25519_64_secret_to_public
  : bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_2_Hacl_Curve25519_64_secret_to_public" 

external _3_Hacl_Curve25519_64_ecdh
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_3_Hacl_Curve25519_64_ecdh" 

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
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))),
  "Hacl_Curve25519_64_ecdh" -> _3_Hacl_Curve25519_64_ecdh
| Function (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Curve25519_64_secret_to_public" ->
  _2_Hacl_Curve25519_64_secret_to_public
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Curve25519_64_scalarmult" -> _1_Hacl_Curve25519_64_scalarmult
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
