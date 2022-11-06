module CI = Cstubs_internals

external _1_Hacl_Keccak_shake128_4x
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_1_Hacl_Keccak_shake128_4x_byte10" "_1_Hacl_Keccak_shake128_4x" 

external _2_Hacl_Impl_Matrix_mod_pow2
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr ->
    unit = "_2_Hacl_Impl_Matrix_mod_pow2" 

external _3_Hacl_Impl_Matrix_matrix_add
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_3_Hacl_Impl_Matrix_matrix_add" 

external _4_Hacl_Impl_Matrix_matrix_sub
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_4_Hacl_Impl_Matrix_matrix_sub" 

external _5_Hacl_Impl_Matrix_matrix_mul
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> _ CI.fatptr -> unit
  = "_5_Hacl_Impl_Matrix_matrix_mul_byte6" "_5_Hacl_Impl_Matrix_matrix_mul" 

external _6_Hacl_Impl_Matrix_matrix_mul_s
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_6_Hacl_Impl_Matrix_matrix_mul_s_byte6" "_6_Hacl_Impl_Matrix_matrix_mul_s" 

external _7_Hacl_Impl_Matrix_matrix_eq
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint16 = "_7_Hacl_Impl_Matrix_matrix_eq" 

external _8_Hacl_Impl_Matrix_matrix_to_lbytes
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> bytes CI.ocaml ->
    unit = "_8_Hacl_Impl_Matrix_matrix_to_lbytes" 

external _9_Hacl_Impl_Matrix_matrix_from_lbytes
  : Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr ->
    unit = "_9_Hacl_Impl_Matrix_matrix_from_lbytes" 

external _10_Hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x
  : Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_10_Hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x" 

external _11_Hacl_Impl_Frodo_Params_frodo_gen_matrix
  : Unsigned.uint8 -> Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr ->
    unit = "_11_Hacl_Impl_Frodo_Params_frodo_gen_matrix" 

external _12_Hacl_Impl_Frodo_Sample_frodo_sample_matrix64
  : Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr ->
    unit = "_12_Hacl_Impl_Frodo_Sample_frodo_sample_matrix64" 

external _13_Hacl_Impl_Frodo_Sample_frodo_sample_matrix640
  : Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr ->
    unit = "_13_Hacl_Impl_Frodo_Sample_frodo_sample_matrix640" 

external _14_Hacl_Impl_Frodo_Sample_frodo_sample_matrix976
  : Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr ->
    unit = "_14_Hacl_Impl_Frodo_Sample_frodo_sample_matrix976" 

external _15_Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344
  : Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr ->
    unit = "_15_Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344" 

external _16_randombytes_ : Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_16_randombytes_" 

external _17_Hacl_Impl_Frodo_Pack_frodo_pack
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr ->
    bytes CI.ocaml -> unit = "_17_Hacl_Impl_Frodo_Pack_frodo_pack" 

external _18_Hacl_Impl_Frodo_Pack_frodo_unpack
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 ->
    bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_18_Hacl_Impl_Frodo_Pack_frodo_unpack" 

external _19_Hacl_Impl_Frodo_Encode_frodo_key_encode
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 ->
    bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_19_Hacl_Impl_Frodo_Encode_frodo_key_encode" 

external _20_Hacl_Impl_Frodo_Encode_frodo_key_decode
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr ->
    bytes CI.ocaml -> unit = "_20_Hacl_Impl_Frodo_Encode_frodo_key_decode" 

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
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void))))),
  "Hacl_Impl_Frodo_Encode_frodo_key_decode" ->
  (fun x1 x2 x3 x4 x6 ->
    let CI.CPointer x5 = x4 in
    _20_Hacl_Impl_Frodo_Encode_frodo_key_decode x1 x2 x3 x5 x6)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Impl_Frodo_Encode_frodo_key_encode" ->
  (fun x7 x8 x9 x10 x11 ->
    let CI.CPointer x12 = x11 in
    _19_Hacl_Impl_Frodo_Encode_frodo_key_encode x7 x8 x9 x10 x12)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Impl_Frodo_Pack_frodo_unpack" ->
  (fun x13 x14 x15 x16 x17 ->
    let CI.CPointer x18 = x17 in
    _18_Hacl_Impl_Frodo_Pack_frodo_unpack x13 x14 x15 x16 x18)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void))))),
  "Hacl_Impl_Frodo_Pack_frodo_pack" ->
  (fun x19 x20 x21 x22 x24 ->
    let CI.CPointer x23 = x22 in
    _17_Hacl_Impl_Frodo_Pack_frodo_pack x19 x20 x21 x23 x24)
| Function
    (CI.Primitive CI.Uint32_t, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "randombytes_" -> _16_randombytes_
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344" ->
  (fun x27 x28 x29 x30 ->
    let CI.CPointer x31 = x30 in
    _15_Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344 x27 x28 x29 x31)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Frodo_Sample_frodo_sample_matrix976" ->
  (fun x32 x33 x34 x35 ->
    let CI.CPointer x36 = x35 in
    _14_Hacl_Impl_Frodo_Sample_frodo_sample_matrix976 x32 x33 x34 x36)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Frodo_Sample_frodo_sample_matrix640" ->
  (fun x37 x38 x39 x40 ->
    let CI.CPointer x41 = x40 in
    _13_Hacl_Impl_Frodo_Sample_frodo_sample_matrix640 x37 x38 x39 x41)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Frodo_Sample_frodo_sample_matrix64" ->
  (fun x42 x43 x44 x45 ->
    let CI.CPointer x46 = x45 in
    _12_Hacl_Impl_Frodo_Sample_frodo_sample_matrix64 x42 x43 x44 x46)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x48; _},
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Frodo_Params_frodo_gen_matrix" ->
  (fun x47 x50 x51 x52 ->
    let CI.CPointer x53 = x52 in
    let x49 = x48 x47 in
    _11_Hacl_Impl_Frodo_Params_frodo_gen_matrix x49 x50 x51 x53)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x" ->
  (fun x54 x55 x56 ->
    let CI.CPointer x57 = x56 in
    _10_Hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x x54 x55 x57)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Matrix_matrix_from_lbytes" ->
  (fun x58 x59 x60 x61 ->
    let CI.CPointer x62 = x61 in
    _9_Hacl_Impl_Matrix_matrix_from_lbytes x58 x59 x60 x62)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_Impl_Matrix_matrix_to_lbytes" ->
  (fun x63 x64 x65 x67 ->
    let CI.CPointer x66 = x65 in
    _8_Hacl_Impl_Matrix_matrix_to_lbytes x63 x64 x66 x67)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint16_t))))),
  "Hacl_Impl_Matrix_matrix_eq" ->
  (fun x68 x69 x70 x72 ->
    let CI.CPointer x73 = x72 in
    let CI.CPointer x71 = x70 in
    _7_Hacl_Impl_Matrix_matrix_eq x68 x69 x71 x73)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))))),
  "Hacl_Impl_Matrix_matrix_mul_s" ->
  (fun x74 x75 x76 x77 x79 x81 ->
    let CI.CPointer x82 = x81 in
    let CI.CPointer x80 = x79 in
    let CI.CPointer x78 = x77 in
    _6_Hacl_Impl_Matrix_matrix_mul_s x74 x75 x76 x78 x80 x82)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))))),
  "Hacl_Impl_Matrix_matrix_mul" ->
  (fun x83 x84 x85 x86 x88 x90 ->
    let CI.CPointer x91 = x90 in
    let CI.CPointer x89 = x88 in
    let CI.CPointer x87 = x86 in
    _5_Hacl_Impl_Matrix_matrix_mul x83 x84 x85 x87 x89 x91)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Matrix_matrix_sub" ->
  (fun x92 x93 x94 x96 ->
    let CI.CPointer x97 = x96 in
    let CI.CPointer x95 = x94 in
    _4_Hacl_Impl_Matrix_matrix_sub x92 x93 x95 x97)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Matrix_matrix_add" ->
  (fun x98 x99 x100 x102 ->
    let CI.CPointer x103 = x102 in
    let CI.CPointer x101 = x100 in
    _3_Hacl_Impl_Matrix_matrix_add x98 x99 x101 x103)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Impl_Matrix_mod_pow2" ->
  (fun x104 x105 x106 x107 ->
    let CI.CPointer x108 = x107 in
    _2_Hacl_Impl_Matrix_mod_pow2 x104 x105 x106 x108)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function
                      (CI.OCaml CI.Bytes,
                       Function
                         (CI.OCaml CI.Bytes,
                          Function
                            (CI.OCaml CI.Bytes,
                             Function (CI.OCaml CI.Bytes, Returns CI.Void)))))))))),
  "Hacl_Keccak_shake128_4x" -> _1_Hacl_Keccak_shake128_4x
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
