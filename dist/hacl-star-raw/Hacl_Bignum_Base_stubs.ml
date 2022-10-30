module CI = Cstubs_internals

external _1_Hacl_Bignum_Convert_bn_from_bytes_be_uint64
  : Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_1_Hacl_Bignum_Convert_bn_from_bytes_be_uint64" 

external _2_Hacl_Bignum_Convert_bn_to_bytes_be_uint64
  : Unsigned.uint32 -> _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_2_Hacl_Bignum_Convert_bn_to_bytes_be_uint64" 

external _3_Hacl_Bignum_Base_mul_wide_add_u64
  : Unsigned.uint64 -> Unsigned.uint64 -> Unsigned.uint64 -> _ CI.fatptr ->
    Unsigned.uint64 = "_3_Hacl_Bignum_Base_mul_wide_add_u64" 

external _4_Hacl_Bignum_Base_mul_wide_add2_u32
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr ->
    Unsigned.uint32 = "_4_Hacl_Bignum_Base_mul_wide_add2_u32" 

external _5_Hacl_Bignum_Base_mul_wide_add2_u64
  : Unsigned.uint64 -> Unsigned.uint64 -> Unsigned.uint64 -> _ CI.fatptr ->
    Unsigned.uint64 = "_5_Hacl_Bignum_Base_mul_wide_add2_u64" 

external _6_Hacl_Bignum_Lib_bn_get_top_index_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32
  = "_6_Hacl_Bignum_Lib_bn_get_top_index_u32" 

external _7_Hacl_Bignum_Lib_bn_get_top_index_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64
  = "_7_Hacl_Bignum_Lib_bn_get_top_index_u64" 

external _8_Hacl_Bignum_Addition_bn_sub_eq_len_u32
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint32 = "_8_Hacl_Bignum_Addition_bn_sub_eq_len_u32" 

external _9_Hacl_Bignum_Addition_bn_sub_eq_len_u64
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint64 = "_9_Hacl_Bignum_Addition_bn_sub_eq_len_u64" 

external _10_Hacl_Bignum_Addition_bn_add_eq_len_u32
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint32 = "_10_Hacl_Bignum_Addition_bn_add_eq_len_u32" 

external _11_Hacl_Bignum_Addition_bn_add_eq_len_u64
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint64 = "_11_Hacl_Bignum_Addition_bn_add_eq_len_u64" 

external _12_Hacl_Bignum_Multiplication_bn_mul_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_12_Hacl_Bignum_Multiplication_bn_mul_u32" 

external _13_Hacl_Bignum_Multiplication_bn_mul_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_13_Hacl_Bignum_Multiplication_bn_mul_u64" 

external _14_Hacl_Bignum_Multiplication_bn_sqr_u32
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_14_Hacl_Bignum_Multiplication_bn_sqr_u32" 

external _15_Hacl_Bignum_Multiplication_bn_sqr_u64
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_15_Hacl_Bignum_Multiplication_bn_sqr_u64" 

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
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum_Multiplication_bn_sqr_u64" ->
  (fun x1 x2 x4 ->
    let CI.CPointer x5 = x4 in
    let CI.CPointer x3 = x2 in
    _15_Hacl_Bignum_Multiplication_bn_sqr_u64 x1 x3 x5)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum_Multiplication_bn_sqr_u32" ->
  (fun x6 x7 x9 ->
    let CI.CPointer x10 = x9 in
    let CI.CPointer x8 = x7 in
    _14_Hacl_Bignum_Multiplication_bn_sqr_u32 x6 x8 x10)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Multiplication_bn_mul_u64" ->
  (fun x11 x12 x14 x15 x17 ->
    let CI.CPointer x18 = x17 in
    let CI.CPointer x16 = x15 in
    let CI.CPointer x13 = x12 in
    _13_Hacl_Bignum_Multiplication_bn_mul_u64 x11 x13 x14 x16 x18)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Multiplication_bn_mul_u32" ->
  (fun x19 x20 x22 x23 x25 ->
    let CI.CPointer x26 = x25 in
    let CI.CPointer x24 = x23 in
    let CI.CPointer x21 = x20 in
    _12_Hacl_Bignum_Multiplication_bn_mul_u32 x19 x21 x22 x24 x26)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t))))),
  "Hacl_Bignum_Addition_bn_add_eq_len_u64" ->
  (fun x27 x28 x30 x32 ->
    let CI.CPointer x33 = x32 in
    let CI.CPointer x31 = x30 in
    let CI.CPointer x29 = x28 in
    _11_Hacl_Bignum_Addition_bn_add_eq_len_u64 x27 x29 x31 x33)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))),
  "Hacl_Bignum_Addition_bn_add_eq_len_u32" ->
  (fun x34 x35 x37 x39 ->
    let CI.CPointer x40 = x39 in
    let CI.CPointer x38 = x37 in
    let CI.CPointer x36 = x35 in
    _10_Hacl_Bignum_Addition_bn_add_eq_len_u32 x34 x36 x38 x40)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t))))),
  "Hacl_Bignum_Addition_bn_sub_eq_len_u64" ->
  (fun x41 x42 x44 x46 ->
    let CI.CPointer x47 = x46 in
    let CI.CPointer x45 = x44 in
    let CI.CPointer x43 = x42 in
    _9_Hacl_Bignum_Addition_bn_sub_eq_len_u64 x41 x43 x45 x47)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))),
  "Hacl_Bignum_Addition_bn_sub_eq_len_u32" ->
  (fun x48 x49 x51 x53 ->
    let CI.CPointer x54 = x53 in
    let CI.CPointer x52 = x51 in
    let CI.CPointer x50 = x49 in
    _8_Hacl_Bignum_Addition_bn_sub_eq_len_u32 x48 x50 x52 x54)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t))),
  "Hacl_Bignum_Lib_bn_get_top_index_u64" ->
  (fun x55 x56 ->
    let CI.CPointer x57 = x56 in
    _7_Hacl_Bignum_Lib_bn_get_top_index_u64 x55 x57)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))),
  "Hacl_Bignum_Lib_bn_get_top_index_u32" ->
  (fun x58 x59 ->
    let CI.CPointer x60 = x59 in
    _6_Hacl_Bignum_Lib_bn_get_top_index_u32 x58 x60)
| Function
    (CI.Primitive CI.Uint64_t,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.Primitive CI.Uint64_t,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t))))),
  "Hacl_Bignum_Base_mul_wide_add2_u64" ->
  (fun x61 x62 x63 x64 ->
    let CI.CPointer x65 = x64 in
    _5_Hacl_Bignum_Base_mul_wide_add2_u64 x61 x62 x63 x65)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))),
  "Hacl_Bignum_Base_mul_wide_add2_u32" ->
  (fun x66 x67 x68 x69 ->
    let CI.CPointer x70 = x69 in
    _4_Hacl_Bignum_Base_mul_wide_add2_u32 x66 x67 x68 x70)
| Function
    (CI.Primitive CI.Uint64_t,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.Primitive CI.Uint64_t,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t))))),
  "Hacl_Bignum_Base_mul_wide_add_u64" ->
  (fun x71 x72 x73 x74 ->
    let CI.CPointer x75 = x74 in
    _3_Hacl_Bignum_Base_mul_wide_add_u64 x71 x72 x73 x75)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Bignum_Convert_bn_to_bytes_be_uint64" ->
  (fun x76 x77 x79 ->
    let CI.CPointer x78 = x77 in
    _2_Hacl_Bignum_Convert_bn_to_bytes_be_uint64 x76 x78 x79)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum_Convert_bn_from_bytes_be_uint64" ->
  (fun x80 x81 x82 ->
    let CI.CPointer x83 = x82 in
    _1_Hacl_Bignum_Convert_bn_from_bytes_be_uint64 x80 x81 x83)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
