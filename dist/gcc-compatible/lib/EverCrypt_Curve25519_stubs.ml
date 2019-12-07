module CI = Cstubs_internals

external _1_EverCrypt_Curve25519_secret_to_public
  : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_1_EverCrypt_Curve25519_secret_to_public" 

external _2_EverCrypt_Curve25519_scalarmult
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_2_EverCrypt_Curve25519_scalarmult" 

external _3_EverCrypt_Curve25519_ecdh
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> bool
  = "_3_EverCrypt_Curve25519_ecdh" 

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
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_Curve25519_ecdh" ->
  (fun x1 x2 x3 ->
    _3_EverCrypt_Curve25519_ecdh (CI.cptr x1) (CI.cptr x2) (CI.cptr x3))
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "EverCrypt_Curve25519_scalarmult" ->
  (fun x4 x5 x6 ->
    _2_EverCrypt_Curve25519_scalarmult (CI.cptr x4) (CI.cptr x5) (CI.cptr x6))
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "EverCrypt_Curve25519_secret_to_public" ->
  (fun x7 x8 ->
    _1_EverCrypt_Curve25519_secret_to_public (CI.cptr x7) (CI.cptr x8))
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
