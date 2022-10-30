module CI = Cstubs_internals

external _1_Hacl_Impl_K256_Point_make_point_at_inf : _ CI.fatptr -> unit
  = "_1_Hacl_Impl_K256_Point_make_point_at_inf" 

external _2_Hacl_Impl_K256_Point_point_negate
  : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_2_Hacl_Impl_K256_Point_point_negate" 

external _3_Hacl_Impl_K256_Point_point_eq
  : _ CI.fatptr -> _ CI.fatptr -> bool = "_3_Hacl_Impl_K256_Point_point_eq" 

external _4_Hacl_Impl_K256_Point_aff_point_decompress_vartime
  : _ CI.fatptr -> _ CI.fatptr -> bytes CI.ocaml -> bool
  = "_4_Hacl_Impl_K256_Point_aff_point_decompress_vartime" 

external _5_Hacl_Impl_K256_Point_aff_point_compress_vartime
  : bytes CI.ocaml -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_5_Hacl_Impl_K256_Point_aff_point_compress_vartime" 

external _6_Hacl_Impl_K256_PointDouble_point_double
  : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_6_Hacl_Impl_K256_PointDouble_point_double" 

external _7_Hacl_Impl_K256_PointAdd_point_add
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_7_Hacl_Impl_K256_PointAdd_point_add" 

external _8_Hacl_Impl_K256_PointMul_point_mul
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_8_Hacl_Impl_K256_PointMul_point_mul" 

external _9_Hacl_K256_ECDSA_ecdsa_sign_hashed_msg
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bool = "_9_Hacl_K256_ECDSA_ecdsa_sign_hashed_msg" 

external _10_Hacl_K256_ECDSA_ecdsa_sign_sha256
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool = "_10_Hacl_K256_ECDSA_ecdsa_sign_sha256" 

external _11_Hacl_K256_ECDSA_ecdsa_verify_hashed_msg
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_11_Hacl_K256_ECDSA_ecdsa_verify_hashed_msg" 

external _12_Hacl_K256_ECDSA_ecdsa_verify_sha256
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bool = "_12_Hacl_K256_ECDSA_ecdsa_verify_sha256" 

external _13_Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize
  : bytes CI.ocaml -> bool
  = "_13_Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize" 

external _14_Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized
  : bytes CI.ocaml -> bool
  = "_14_Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized" 

external _15_Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bool = "_15_Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg" 

external _16_Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool
  = "_16_Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256" 

external _17_Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_17_Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg" 

external _18_Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bool = "_18_Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256" 

external _19_Hacl_K256_ECDSA_public_key_uncompressed_to_raw
  : bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_19_Hacl_K256_ECDSA_public_key_uncompressed_to_raw" 

external _20_Hacl_K256_ECDSA_public_key_uncompressed_from_raw
  : bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_20_Hacl_K256_ECDSA_public_key_uncompressed_from_raw" 

external _21_Hacl_K256_ECDSA_public_key_compressed_to_raw
  : bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_21_Hacl_K256_ECDSA_public_key_compressed_to_raw" 

external _22_Hacl_K256_ECDSA_public_key_compressed_from_raw
  : bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_22_Hacl_K256_ECDSA_public_key_compressed_from_raw" 

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
| Function (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_K256_ECDSA_public_key_compressed_from_raw" ->
  _22_Hacl_K256_ECDSA_public_key_compressed_from_raw
| Function
    (CI.OCaml CI.Bytes,
     Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))),
  "Hacl_K256_ECDSA_public_key_compressed_to_raw" ->
  _21_Hacl_K256_ECDSA_public_key_compressed_to_raw
| Function (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_K256_ECDSA_public_key_uncompressed_from_raw" ->
  _20_Hacl_K256_ECDSA_public_key_uncompressed_from_raw
| Function
    (CI.OCaml CI.Bytes,
     Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))),
  "Hacl_K256_ECDSA_public_key_uncompressed_to_raw" ->
  _19_Hacl_K256_ECDSA_public_key_uncompressed_to_raw
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))))),
  "Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256" ->
  _18_Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))),
  "Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg" ->
  _17_Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256" ->
  _16_Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))))),
  "Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg" ->
  _15_Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg
| Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)),
  "Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized" ->
  _14_Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized
| Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)),
  "Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize" ->
  _13_Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))))),
  "Hacl_K256_ECDSA_ecdsa_verify_sha256" ->
  _12_Hacl_K256_ECDSA_ecdsa_verify_sha256
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))),
  "Hacl_K256_ECDSA_ecdsa_verify_hashed_msg" ->
  _11_Hacl_K256_ECDSA_ecdsa_verify_hashed_msg
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_K256_ECDSA_ecdsa_sign_sha256" ->
  _10_Hacl_K256_ECDSA_ecdsa_sign_sha256
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))))),
  "Hacl_K256_ECDSA_ecdsa_sign_hashed_msg" ->
  _9_Hacl_K256_ECDSA_ecdsa_sign_hashed_msg
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_K256_PointMul_point_mul" ->
  (fun x43 x45 x47 ->
    let CI.CPointer x48 = x47 in
    let CI.CPointer x46 = x45 in
    let CI.CPointer x44 = x43 in
    _8_Hacl_Impl_K256_PointMul_point_mul x44 x46 x48)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_K256_PointAdd_point_add" ->
  (fun x49 x51 x53 ->
    let CI.CPointer x54 = x53 in
    let CI.CPointer x52 = x51 in
    let CI.CPointer x50 = x49 in
    _7_Hacl_Impl_K256_PointAdd_point_add x50 x52 x54)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_K256_PointDouble_point_double" ->
  (fun x55 x57 ->
    let CI.CPointer x58 = x57 in
    let CI.CPointer x56 = x55 in
    _6_Hacl_Impl_K256_PointDouble_point_double x56 x58)
| Function
    (CI.OCaml CI.Bytes,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_K256_Point_aff_point_compress_vartime" ->
  (fun x59 x60 x62 ->
    let CI.CPointer x63 = x62 in
    let CI.CPointer x61 = x60 in
    _5_Hacl_Impl_K256_Point_aff_point_compress_vartime x59 x61 x63)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool)))),
  "Hacl_Impl_K256_Point_aff_point_decompress_vartime" ->
  (fun x64 x66 x68 ->
    let CI.CPointer x67 = x66 in
    let CI.CPointer x65 = x64 in
    _4_Hacl_Impl_K256_Point_aff_point_decompress_vartime x65 x67 x68)
| Function
    (CI.Pointer _, Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))),
  "Hacl_Impl_K256_Point_point_eq" ->
  (fun x69 x71 ->
    let CI.CPointer x72 = x71 in
    let CI.CPointer x70 = x69 in _3_Hacl_Impl_K256_Point_point_eq x70 x72)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_K256_Point_point_negate" ->
  (fun x73 x75 ->
    let CI.CPointer x76 = x75 in
    let CI.CPointer x74 = x73 in _2_Hacl_Impl_K256_Point_point_negate x74 x76)
| Function (CI.Pointer _, Returns CI.Void),
  "Hacl_Impl_K256_Point_make_point_at_inf" ->
  (fun x77 ->
    let CI.CPointer x78 = x77 in
    _1_Hacl_Impl_K256_Point_make_point_at_inf x78)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
