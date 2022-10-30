module CI = Cstubs_internals

external _1_Hacl_Impl_P256_LowLevel_toUint8
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_1_Hacl_Impl_P256_LowLevel_toUint8" 

external _2_Hacl_Impl_P256_LowLevel_changeEndian : _ CI.fatptr -> unit
  = "_2_Hacl_Impl_P256_LowLevel_changeEndian" 

external _3_Hacl_Impl_P256_LowLevel_toUint64ChangeEndian
  : bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_3_Hacl_Impl_P256_LowLevel_toUint64ChangeEndian" 

external _4_Hacl_Impl_P256_Core_isPointAtInfinityPrivate
  : _ CI.fatptr -> Unsigned.uint64
  = "_4_Hacl_Impl_P256_Core_isPointAtInfinityPrivate" 

external _5_Hacl_Impl_P256_Core_secretToPublic
  : _ CI.fatptr -> bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_5_Hacl_Impl_P256_Core_secretToPublic" 

external _6_Hacl_Impl_P256_DH__ecp256dh_r
  : _ CI.fatptr -> _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint64
  = "_6_Hacl_Impl_P256_DH__ecp256dh_r" 

external _7_Hacl_P256_ecdsa_sign_p256_sha2
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_7_Hacl_P256_ecdsa_sign_p256_sha2" 

external _8_Hacl_P256_ecdsa_sign_p256_sha384
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_8_Hacl_P256_ecdsa_sign_p256_sha384" 

external _9_Hacl_P256_ecdsa_sign_p256_sha512
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_9_Hacl_P256_ecdsa_sign_p256_sha512" 

external _10_Hacl_P256_ecdsa_sign_p256_without_hash
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_10_Hacl_P256_ecdsa_sign_p256_without_hash" 

external _11_Hacl_P256_ecdsa_verif_p256_sha2
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_11_Hacl_P256_ecdsa_verif_p256_sha2" 

external _12_Hacl_P256_ecdsa_verif_p256_sha384
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_12_Hacl_P256_ecdsa_verif_p256_sha384" 

external _13_Hacl_P256_ecdsa_verif_p256_sha512
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_13_Hacl_P256_ecdsa_verif_p256_sha512" 

external _14_Hacl_P256_ecdsa_verif_without_hash
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_14_Hacl_P256_ecdsa_verif_without_hash" 

external _15_Hacl_P256_validate_public_key : bytes CI.ocaml -> bool
  = "_15_Hacl_P256_validate_public_key" 

external _16_Hacl_P256_validate_private_key : bytes CI.ocaml -> bool
  = "_16_Hacl_P256_validate_private_key" 

external _17_Hacl_P256_uncompressed_to_raw
  : bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_17_Hacl_P256_uncompressed_to_raw" 

external _18_Hacl_P256_compressed_to_raw
  : bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_18_Hacl_P256_compressed_to_raw" 

external _19_Hacl_P256_raw_to_uncompressed
  : bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_19_Hacl_P256_raw_to_uncompressed" 

external _20_Hacl_P256_raw_to_compressed
  : bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_20_Hacl_P256_raw_to_compressed" 

external _21_Hacl_P256_dh_initiator
  : bytes CI.ocaml -> bytes CI.ocaml -> bool = "_21_Hacl_P256_dh_initiator" 

external _22_Hacl_P256_dh_responder
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_22_Hacl_P256_dh_responder" 

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
  "Hacl_P256_dh_responder" -> _22_Hacl_P256_dh_responder
| Function
    (CI.OCaml CI.Bytes,
     Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))),
  "Hacl_P256_dh_initiator" -> _21_Hacl_P256_dh_initiator
| Function (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_P256_raw_to_compressed" -> _20_Hacl_P256_raw_to_compressed
| Function (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_P256_raw_to_uncompressed" -> _19_Hacl_P256_raw_to_uncompressed
| Function
    (CI.OCaml CI.Bytes,
     Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))),
  "Hacl_P256_compressed_to_raw" -> _18_Hacl_P256_compressed_to_raw
| Function
    (CI.OCaml CI.Bytes,
     Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))),
  "Hacl_P256_uncompressed_to_raw" -> _17_Hacl_P256_uncompressed_to_raw
| Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)),
  "Hacl_P256_validate_private_key" -> _16_Hacl_P256_validate_private_key
| Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)),
  "Hacl_P256_validate_public_key" -> _15_Hacl_P256_validate_public_key
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_P256_ecdsa_verif_without_hash" ->
  _14_Hacl_P256_ecdsa_verif_without_hash
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_P256_ecdsa_verif_p256_sha512" ->
  _13_Hacl_P256_ecdsa_verif_p256_sha512
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_P256_ecdsa_verif_p256_sha384" ->
  _12_Hacl_P256_ecdsa_verif_p256_sha384
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_P256_ecdsa_verif_p256_sha2" -> _11_Hacl_P256_ecdsa_verif_p256_sha2
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_P256_ecdsa_sign_p256_without_hash" ->
  _10_Hacl_P256_ecdsa_sign_p256_without_hash
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_P256_ecdsa_sign_p256_sha512" -> _9_Hacl_P256_ecdsa_sign_p256_sha512
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_P256_ecdsa_sign_p256_sha384" -> _8_Hacl_P256_ecdsa_sign_p256_sha384
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_P256_ecdsa_sign_p256_sha2" -> _7_Hacl_P256_ecdsa_sign_p256_sha2
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint64_t)))),
  "Hacl_Impl_P256_DH__ecp256dh_r" ->
  (fun x56 x58 x60 ->
    let CI.CPointer x59 = x58 in
    let CI.CPointer x57 = x56 in _6_Hacl_Impl_P256_DH__ecp256dh_r x57 x59 x60)
| Function
    (CI.Pointer _,
     Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_P256_Core_secretToPublic" ->
  (fun x61 x63 x64 ->
    let CI.CPointer x65 = x64 in
    let CI.CPointer x62 = x61 in
    _5_Hacl_Impl_P256_Core_secretToPublic x62 x63 x65)
| Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t)),
  "Hacl_Impl_P256_Core_isPointAtInfinityPrivate" ->
  (fun x66 ->
    let CI.CPointer x67 = x66 in
    _4_Hacl_Impl_P256_Core_isPointAtInfinityPrivate x67)
| Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_P256_LowLevel_toUint64ChangeEndian" ->
  (fun x68 x69 ->
    let CI.CPointer x70 = x69 in
    _3_Hacl_Impl_P256_LowLevel_toUint64ChangeEndian x68 x70)
| Function (CI.Pointer _, Returns CI.Void),
  "Hacl_Impl_P256_LowLevel_changeEndian" ->
  (fun x71 ->
    let CI.CPointer x72 = x71 in _2_Hacl_Impl_P256_LowLevel_changeEndian x72)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Impl_P256_LowLevel_toUint8" ->
  (fun x73 x75 ->
    let CI.CPointer x74 = x73 in _1_Hacl_Impl_P256_LowLevel_toUint8 x74 x75)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
