module CI = Cstubs_internals

external _1_EverCrypt_HMAC_compute_sha1
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    Unsigned.uint32 -> unit = "_1_EverCrypt_HMAC_compute_sha1" 

external _2_EverCrypt_HMAC_compute_sha2_256
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    Unsigned.uint32 -> unit = "_2_EverCrypt_HMAC_compute_sha2_256" 

external _3_EverCrypt_HMAC_compute_sha2_384
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    Unsigned.uint32 -> unit = "_3_EverCrypt_HMAC_compute_sha2_384" 

external _4_EverCrypt_HMAC_compute_sha2_512
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    Unsigned.uint32 -> unit = "_4_EverCrypt_HMAC_compute_sha2_512" 

external _5_EverCrypt_HMAC_is_supported_alg : Unsigned.uint8 -> bool
  = "_5_EverCrypt_HMAC_is_supported_alg" 

external _6_EverCrypt_HMAC_compute
  : Unsigned.uint8 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> Unsigned.uint32 -> unit
  = "_6_EverCrypt_HMAC_compute_byte6" "_6_EverCrypt_HMAC_compute" 

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
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "EverCrypt_HMAC_compute" ->
  (fun x1 x4 x5 x6 x7 x8 ->
    let x3 = x2 x1 in
    _6_EverCrypt_HMAC_compute x3 (CI.cptr x4) (CI.cptr x5) x6 (CI.cptr x7) x8)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x10; _},
     Returns (CI.Primitive CI.Bool)),
  "EverCrypt_HMAC_is_supported_alg" ->
  (fun x9 -> let x11 = x10 x9 in _5_EverCrypt_HMAC_is_supported_alg x11)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_sha2_512" ->
  (fun x12 x13 x14 x15 x16 ->
    _4_EverCrypt_HMAC_compute_sha2_512 (CI.cptr x12) (CI.cptr x13) x14
    (CI.cptr x15) x16)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_sha2_384" ->
  (fun x17 x18 x19 x20 x21 ->
    _3_EverCrypt_HMAC_compute_sha2_384 (CI.cptr x17) (CI.cptr x18) x19
    (CI.cptr x20) x21)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_sha2_256" ->
  (fun x22 x23 x24 x25 x26 ->
    _2_EverCrypt_HMAC_compute_sha2_256 (CI.cptr x22) (CI.cptr x23) x24
    (CI.cptr x25) x26)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "EverCrypt_HMAC_compute_sha1" ->
  (fun x27 x28 x29 x30 x31 ->
    _1_EverCrypt_HMAC_compute_sha1 (CI.cptr x27) (CI.cptr x28) x29
    (CI.cptr x30) x31)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
