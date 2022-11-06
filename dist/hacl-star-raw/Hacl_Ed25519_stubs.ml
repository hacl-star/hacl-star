module CI = Cstubs_internals

external _1_Hacl_Bignum25519_reduce_513 : _ CI.fatptr -> unit
  = "_1_Hacl_Bignum25519_reduce_513" 

external _2_Hacl_Bignum25519_inverse : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_2_Hacl_Bignum25519_inverse" 

external _3_Hacl_Bignum25519_load_51 : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_3_Hacl_Bignum25519_load_51" 

external _4_Hacl_Bignum25519_store_51 : bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_4_Hacl_Bignum25519_store_51" 

external _5_Hacl_Impl_Ed25519_PointDouble_point_double
  : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_5_Hacl_Impl_Ed25519_PointDouble_point_double" 

external _6_Hacl_Impl_Ed25519_PointAdd_point_add
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_6_Hacl_Impl_Ed25519_PointAdd_point_add" 

external _7_Hacl_Impl_Ed25519_PointConstants_make_point_inf
  : _ CI.fatptr -> unit
  = "_7_Hacl_Impl_Ed25519_PointConstants_make_point_inf" 

external _8_Hacl_Impl_Ed25519_PointDecompress_point_decompress
  : _ CI.fatptr -> bytes CI.ocaml -> bool
  = "_8_Hacl_Impl_Ed25519_PointDecompress_point_decompress" 

external _9_Hacl_Impl_Ed25519_PointCompress_point_compress
  : bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_9_Hacl_Impl_Ed25519_PointCompress_point_compress" 

external _10_Hacl_Impl_Ed25519_PointEqual_point_equal
  : _ CI.fatptr -> _ CI.fatptr -> bool
  = "_10_Hacl_Impl_Ed25519_PointEqual_point_equal" 

external _11_Hacl_Impl_Ed25519_PointNegate_point_negate
  : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_11_Hacl_Impl_Ed25519_PointNegate_point_negate" 

external _12_Hacl_Impl_Ed25519_Ladder_point_mul
  : _ CI.fatptr -> bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_12_Hacl_Impl_Ed25519_Ladder_point_mul" 

external _13_Hacl_Ed25519_secret_to_public
  : bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_13_Hacl_Ed25519_secret_to_public" 

external _14_Hacl_Ed25519_expand_keys
  : bytes CI.ocaml -> bytes CI.ocaml -> unit = "_14_Hacl_Ed25519_expand_keys" 

external _15_Hacl_Ed25519_sign_expanded
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    unit = "_15_Hacl_Ed25519_sign_expanded" 

external _16_Hacl_Ed25519_sign
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    unit = "_16_Hacl_Ed25519_sign" 

external _17_Hacl_Ed25519_verify
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    bool = "_17_Hacl_Ed25519_verify" 

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
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))))),
  "Hacl_Ed25519_verify" -> _17_Hacl_Ed25519_verify
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_Ed25519_sign" -> _16_Hacl_Ed25519_sign
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_Ed25519_sign_expanded" -> _15_Hacl_Ed25519_sign_expanded
| Function (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Ed25519_expand_keys" -> _14_Hacl_Ed25519_expand_keys
| Function (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Ed25519_secret_to_public" -> _13_Hacl_Ed25519_secret_to_public
| Function
    (CI.Pointer _,
     Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_Ed25519_Ladder_point_mul" ->
  (fun x17 x19 x20 ->
    let CI.CPointer x21 = x20 in
    let CI.CPointer x18 = x17 in
    _12_Hacl_Impl_Ed25519_Ladder_point_mul x18 x19 x21)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_Ed25519_PointNegate_point_negate" ->
  (fun x22 x24 ->
    let CI.CPointer x25 = x24 in
    let CI.CPointer x23 = x22 in
    _11_Hacl_Impl_Ed25519_PointNegate_point_negate x23 x25)
| Function
    (CI.Pointer _, Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))),
  "Hacl_Impl_Ed25519_PointEqual_point_equal" ->
  (fun x26 x28 ->
    let CI.CPointer x29 = x28 in
    let CI.CPointer x27 = x26 in
    _10_Hacl_Impl_Ed25519_PointEqual_point_equal x27 x29)
| Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_Ed25519_PointCompress_point_compress" ->
  (fun x30 x31 ->
    let CI.CPointer x32 = x31 in
    _9_Hacl_Impl_Ed25519_PointCompress_point_compress x30 x32)
| Function
    (CI.Pointer _,
     Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))),
  "Hacl_Impl_Ed25519_PointDecompress_point_decompress" ->
  (fun x33 x35 ->
    let CI.CPointer x34 = x33 in
    _8_Hacl_Impl_Ed25519_PointDecompress_point_decompress x34 x35)
| Function (CI.Pointer _, Returns CI.Void),
  "Hacl_Impl_Ed25519_PointConstants_make_point_inf" ->
  (fun x36 ->
    let CI.CPointer x37 = x36 in
    _7_Hacl_Impl_Ed25519_PointConstants_make_point_inf x37)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_Ed25519_PointAdd_point_add" ->
  (fun x38 x40 x42 ->
    let CI.CPointer x43 = x42 in
    let CI.CPointer x41 = x40 in
    let CI.CPointer x39 = x38 in
    _6_Hacl_Impl_Ed25519_PointAdd_point_add x39 x41 x43)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_Ed25519_PointDouble_point_double" ->
  (fun x44 x46 ->
    let CI.CPointer x47 = x46 in
    let CI.CPointer x45 = x44 in
    _5_Hacl_Impl_Ed25519_PointDouble_point_double x45 x47)
| Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Bignum25519_store_51" ->
  (fun x48 x49 ->
    let CI.CPointer x50 = x49 in _4_Hacl_Bignum25519_store_51 x48 x50)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Bignum25519_load_51" ->
  (fun x51 x53 ->
    let CI.CPointer x52 = x51 in _3_Hacl_Bignum25519_load_51 x52 x53)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Bignum25519_inverse" ->
  (fun x54 x56 ->
    let CI.CPointer x57 = x56 in
    let CI.CPointer x55 = x54 in _2_Hacl_Bignum25519_inverse x55 x57)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Bignum25519_reduce_513" ->
  (fun x58 ->
    let CI.CPointer x59 = x58 in _1_Hacl_Bignum25519_reduce_513 x59)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
