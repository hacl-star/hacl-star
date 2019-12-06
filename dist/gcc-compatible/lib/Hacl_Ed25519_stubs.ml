module CI = Cstubs_internals

external _1_Hacl_Ed25519_sign
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr -> unit
  = "_1_Hacl_Ed25519_sign" 

external _2_Hacl_Ed25519_verify
  : _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> bool
  = "_2_Hacl_Ed25519_verify" 

external _3_Hacl_Ed25519_secret_to_public
  : _ CI.fatptr -> _ CI.fatptr -> unit = "_3_Hacl_Ed25519_secret_to_public" 

external _4_Hacl_Ed25519_expand_keys : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_4_Hacl_Ed25519_expand_keys" 

external _5_Hacl_Ed25519_sign_expanded
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr -> unit
  = "_5_Hacl_Ed25519_sign_expanded" 

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
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Ed25519_sign_expanded" ->
  (fun x1 x2 x3 x4 ->
    _5_Hacl_Ed25519_sign_expanded (CI.cptr x1) (CI.cptr x2) x3 (CI.cptr x4))
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Ed25519_expand_keys" ->
  (fun x5 x6 -> _4_Hacl_Ed25519_expand_keys (CI.cptr x5) (CI.cptr x6))
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Ed25519_secret_to_public" ->
  (fun x7 x8 -> _3_Hacl_Ed25519_secret_to_public (CI.cptr x7) (CI.cptr x8))
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))))),
  "Hacl_Ed25519_verify" ->
  (fun x9 x10 x11 x12 ->
    _2_Hacl_Ed25519_verify (CI.cptr x9) x10 (CI.cptr x11) (CI.cptr x12))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Ed25519_sign" ->
  (fun x13 x14 x15 x16 ->
    _1_Hacl_Ed25519_sign (CI.cptr x13) (CI.cptr x14) x15 (CI.cptr x16))
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
