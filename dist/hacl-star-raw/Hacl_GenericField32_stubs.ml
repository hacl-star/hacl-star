module CI = Cstubs_internals

external _1_Hacl_GenericField32_field_modulus_check
  : Unsigned.uint32 -> _ CI.fatptr -> bool
  = "_1_Hacl_GenericField32_field_modulus_check" 

external _2_Hacl_GenericField32_field_init
  : Unsigned.uint32 -> _ CI.fatptr -> CI.voidp
  = "_2_Hacl_GenericField32_field_init" 

external _3_Hacl_GenericField32_field_free : _ CI.fatptr -> unit
  = "_3_Hacl_GenericField32_field_free" 

external _4_Hacl_GenericField32_field_get_len
  : _ CI.fatptr -> Unsigned.uint32 = "_4_Hacl_GenericField32_field_get_len" 

external _5_Hacl_GenericField32_to_field
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_5_Hacl_GenericField32_to_field" 

external _6_Hacl_GenericField32_from_field
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_6_Hacl_GenericField32_from_field" 

external _7_Hacl_GenericField32_add
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_7_Hacl_GenericField32_add" 

external _8_Hacl_GenericField32_sub
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_8_Hacl_GenericField32_sub" 

external _9_Hacl_GenericField32_mul
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_9_Hacl_GenericField32_mul" 

external _10_Hacl_GenericField32_sqr
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_10_Hacl_GenericField32_sqr" 

external _11_Hacl_GenericField32_one : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_11_Hacl_GenericField32_one" 

external _12_Hacl_GenericField32_exp_consttime
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_12_Hacl_GenericField32_exp_consttime" 

external _13_Hacl_GenericField32_exp_vartime
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_13_Hacl_GenericField32_exp_vartime" 

external _14_Hacl_GenericField32_inverse
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_14_Hacl_GenericField32_inverse" 

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
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_GenericField32_inverse" ->
  (fun x1 x3 x5 ->
    let CI.CPointer x6 = x5 in
    let CI.CPointer x4 = x3 in
    let CI.CPointer x2 = x1 in _14_Hacl_GenericField32_inverse x2 x4 x6)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_GenericField32_exp_vartime" ->
  (fun x7 x9 x11 x12 x14 ->
    let CI.CPointer x15 = x14 in
    let CI.CPointer x13 = x12 in
    let CI.CPointer x10 = x9 in
    let CI.CPointer x8 = x7 in
    _13_Hacl_GenericField32_exp_vartime x8 x10 x11 x13 x15)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_GenericField32_exp_consttime" ->
  (fun x16 x18 x20 x21 x23 ->
    let CI.CPointer x24 = x23 in
    let CI.CPointer x22 = x21 in
    let CI.CPointer x19 = x18 in
    let CI.CPointer x17 = x16 in
    _12_Hacl_GenericField32_exp_consttime x17 x19 x20 x22 x24)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_GenericField32_one" ->
  (fun x25 x27 ->
    let CI.CPointer x28 = x27 in
    let CI.CPointer x26 = x25 in _11_Hacl_GenericField32_one x26 x28)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_GenericField32_sqr" ->
  (fun x29 x31 x33 ->
    let CI.CPointer x34 = x33 in
    let CI.CPointer x32 = x31 in
    let CI.CPointer x30 = x29 in _10_Hacl_GenericField32_sqr x30 x32 x34)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_GenericField32_mul" ->
  (fun x35 x37 x39 x41 ->
    let CI.CPointer x42 = x41 in
    let CI.CPointer x40 = x39 in
    let CI.CPointer x38 = x37 in
    let CI.CPointer x36 = x35 in _9_Hacl_GenericField32_mul x36 x38 x40 x42)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_GenericField32_sub" ->
  (fun x43 x45 x47 x49 ->
    let CI.CPointer x50 = x49 in
    let CI.CPointer x48 = x47 in
    let CI.CPointer x46 = x45 in
    let CI.CPointer x44 = x43 in _8_Hacl_GenericField32_sub x44 x46 x48 x50)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_GenericField32_add" ->
  (fun x51 x53 x55 x57 ->
    let CI.CPointer x58 = x57 in
    let CI.CPointer x56 = x55 in
    let CI.CPointer x54 = x53 in
    let CI.CPointer x52 = x51 in _7_Hacl_GenericField32_add x52 x54 x56 x58)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_GenericField32_from_field" ->
  (fun x59 x61 x63 ->
    let CI.CPointer x64 = x63 in
    let CI.CPointer x62 = x61 in
    let CI.CPointer x60 = x59 in
    _6_Hacl_GenericField32_from_field x60 x62 x64)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_GenericField32_to_field" ->
  (fun x65 x67 x69 ->
    let CI.CPointer x70 = x69 in
    let CI.CPointer x68 = x67 in
    let CI.CPointer x66 = x65 in _5_Hacl_GenericField32_to_field x66 x68 x70)
| Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)),
  "Hacl_GenericField32_field_get_len" ->
  (fun x71 ->
    let CI.CPointer x72 = x71 in _4_Hacl_GenericField32_field_get_len x72)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_GenericField32_field_free" ->
  (fun x73 ->
    let CI.CPointer x74 = x73 in _3_Hacl_GenericField32_field_free x74)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Returns (CI.Pointer x78))),
  "Hacl_GenericField32_field_init" ->
  (fun x75 x76 ->
    let CI.CPointer x77 = x76 in
    CI.make_ptr x78 (_2_Hacl_GenericField32_field_init x75 x77))
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))),
  "Hacl_GenericField32_field_modulus_check" ->
  (fun x79 x80 ->
    let CI.CPointer x81 = x80 in
    _1_Hacl_GenericField32_field_modulus_check x79 x81)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
