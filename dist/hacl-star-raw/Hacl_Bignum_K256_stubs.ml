module CI = Cstubs_internals

external _1_Hacl_K256_Field_is_felem_zero_vartime : _ CI.fatptr -> bool
  = "_1_Hacl_K256_Field_is_felem_zero_vartime" 

external _2_Hacl_K256_Field_is_felem_eq_vartime
  : _ CI.fatptr -> _ CI.fatptr -> bool
  = "_2_Hacl_K256_Field_is_felem_eq_vartime" 

external _3_Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime
  : _ CI.fatptr -> bool
  = "_3_Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime" 

external _4_Hacl_K256_Field_load_felem
  : _ CI.fatptr -> bytes CI.ocaml -> unit = "_4_Hacl_K256_Field_load_felem" 

external _5_Hacl_K256_Field_load_felem_vartime
  : _ CI.fatptr -> bytes CI.ocaml -> bool
  = "_5_Hacl_K256_Field_load_felem_vartime" 

external _6_Hacl_K256_Field_store_felem
  : bytes CI.ocaml -> _ CI.fatptr -> unit = "_6_Hacl_K256_Field_store_felem" 

external _7_Hacl_K256_Field_fmul_small_num
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64 -> unit
  = "_7_Hacl_K256_Field_fmul_small_num" 

external _8_Hacl_K256_Field_fadd
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_8_Hacl_K256_Field_fadd" 

external _9_Hacl_K256_Field_fsub
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64 -> unit
  = "_9_Hacl_K256_Field_fsub" 

external _10_Hacl_K256_Field_fmul
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_10_Hacl_K256_Field_fmul" 

external _11_Hacl_K256_Field_fsqr : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_11_Hacl_K256_Field_fsqr" 

external _12_Hacl_K256_Field_fnormalize_weak
  : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_12_Hacl_K256_Field_fnormalize_weak" 

external _13_Hacl_K256_Field_fnormalize : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_13_Hacl_K256_Field_fnormalize" 

external _14_Hacl_K256_Field_fnegate_conditional_vartime
  : _ CI.fatptr -> bool -> unit
  = "_14_Hacl_K256_Field_fnegate_conditional_vartime" 

external _15_Hacl_Impl_K256_Finv_fsquare_times_in_place
  : _ CI.fatptr -> Unsigned.uint32 -> unit
  = "_15_Hacl_Impl_K256_Finv_fsquare_times_in_place" 

external _16_Hacl_Impl_K256_Finv_fsquare_times
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> unit
  = "_16_Hacl_Impl_K256_Finv_fsquare_times" 

external _17_Hacl_Impl_K256_Finv_fexp_223_23
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_17_Hacl_Impl_K256_Finv_fexp_223_23" 

external _18_Hacl_Impl_K256_Finv_finv : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_18_Hacl_Impl_K256_Finv_finv" 

external _19_Hacl_Impl_K256_Finv_fsqrt : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_19_Hacl_Impl_K256_Finv_fsqrt" 

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
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_K256_Finv_fsqrt" ->
  (fun x1 x3 ->
    let CI.CPointer x4 = x3 in
    let CI.CPointer x2 = x1 in _19_Hacl_Impl_K256_Finv_fsqrt x2 x4)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_K256_Finv_finv" ->
  (fun x5 x7 ->
    let CI.CPointer x8 = x7 in
    let CI.CPointer x6 = x5 in _18_Hacl_Impl_K256_Finv_finv x6 x8)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_K256_Finv_fexp_223_23" ->
  (fun x9 x11 x13 ->
    let CI.CPointer x14 = x13 in
    let CI.CPointer x12 = x11 in
    let CI.CPointer x10 = x9 in
    _17_Hacl_Impl_K256_Finv_fexp_223_23 x10 x12 x14)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _, Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Impl_K256_Finv_fsquare_times" ->
  (fun x15 x17 x19 ->
    let CI.CPointer x18 = x17 in
    let CI.CPointer x16 = x15 in
    _16_Hacl_Impl_K256_Finv_fsquare_times x16 x18 x19)
| Function
    (CI.Pointer _, Function (CI.Primitive CI.Uint32_t, Returns CI.Void)),
  "Hacl_Impl_K256_Finv_fsquare_times_in_place" ->
  (fun x20 x22 ->
    let CI.CPointer x21 = x20 in
    _15_Hacl_Impl_K256_Finv_fsquare_times_in_place x21 x22)
| Function (CI.Pointer _, Function (CI.Primitive CI.Bool, Returns CI.Void)),
  "Hacl_K256_Field_fnegate_conditional_vartime" ->
  (fun x23 x25 ->
    let CI.CPointer x24 = x23 in
    _14_Hacl_K256_Field_fnegate_conditional_vartime x24 x25)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_K256_Field_fnormalize" ->
  (fun x26 x28 ->
    let CI.CPointer x29 = x28 in
    let CI.CPointer x27 = x26 in _13_Hacl_K256_Field_fnormalize x27 x29)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_K256_Field_fnormalize_weak" ->
  (fun x30 x32 ->
    let CI.CPointer x33 = x32 in
    let CI.CPointer x31 = x30 in _12_Hacl_K256_Field_fnormalize_weak x31 x33)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_K256_Field_fsqr" ->
  (fun x34 x36 ->
    let CI.CPointer x37 = x36 in
    let CI.CPointer x35 = x34 in _11_Hacl_K256_Field_fsqr x35 x37)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_K256_Field_fmul" ->
  (fun x38 x40 x42 ->
    let CI.CPointer x43 = x42 in
    let CI.CPointer x41 = x40 in
    let CI.CPointer x39 = x38 in _10_Hacl_K256_Field_fmul x39 x41 x43)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Primitive CI.Uint64_t, Returns CI.Void)))),
  "Hacl_K256_Field_fsub" ->
  (fun x44 x46 x48 x50 ->
    let CI.CPointer x49 = x48 in
    let CI.CPointer x47 = x46 in
    let CI.CPointer x45 = x44 in _9_Hacl_K256_Field_fsub x45 x47 x49 x50)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_K256_Field_fadd" ->
  (fun x51 x53 x55 ->
    let CI.CPointer x56 = x55 in
    let CI.CPointer x54 = x53 in
    let CI.CPointer x52 = x51 in _8_Hacl_K256_Field_fadd x52 x54 x56)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _, Function (CI.Primitive CI.Uint64_t, Returns CI.Void))),
  "Hacl_K256_Field_fmul_small_num" ->
  (fun x57 x59 x61 ->
    let CI.CPointer x60 = x59 in
    let CI.CPointer x58 = x57 in
    _7_Hacl_K256_Field_fmul_small_num x58 x60 x61)
| Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_K256_Field_store_felem" ->
  (fun x62 x63 ->
    let CI.CPointer x64 = x63 in _6_Hacl_K256_Field_store_felem x62 x64)
| Function
    (CI.Pointer _,
     Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))),
  "Hacl_K256_Field_load_felem_vartime" ->
  (fun x65 x67 ->
    let CI.CPointer x66 = x65 in
    _5_Hacl_K256_Field_load_felem_vartime x66 x67)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_K256_Field_load_felem" ->
  (fun x68 x70 ->
    let CI.CPointer x69 = x68 in _4_Hacl_K256_Field_load_felem x69 x70)
| Function (CI.Pointer _, Returns (CI.Primitive CI.Bool)),
  "Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime" ->
  (fun x71 ->
    let CI.CPointer x72 = x71 in
    _3_Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime x72)
| Function
    (CI.Pointer _, Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))),
  "Hacl_K256_Field_is_felem_eq_vartime" ->
  (fun x73 x75 ->
    let CI.CPointer x76 = x75 in
    let CI.CPointer x74 = x73 in
    _2_Hacl_K256_Field_is_felem_eq_vartime x74 x76)
| Function (CI.Pointer _, Returns (CI.Primitive CI.Bool)),
  "Hacl_K256_Field_is_felem_zero_vartime" ->
  (fun x77 ->
    let CI.CPointer x78 = x77 in _1_Hacl_K256_Field_is_felem_zero_vartime x78)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
