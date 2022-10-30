module CI = Cstubs_internals

external _1_Hacl_Bignum32_add
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint32 = "_1_Hacl_Bignum32_add" 

external _2_Hacl_Bignum32_sub
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint32 = "_2_Hacl_Bignum32_sub" 

external _3_Hacl_Bignum32_add_mod
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_3_Hacl_Bignum32_add_mod" 

external _4_Hacl_Bignum32_sub_mod
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_4_Hacl_Bignum32_sub_mod" 

external _5_Hacl_Bignum32_mul
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_5_Hacl_Bignum32_mul" 

external _6_Hacl_Bignum32_sqr
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_6_Hacl_Bignum32_sqr" 

external _7_Hacl_Bignum32_mod
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> bool
  = "_7_Hacl_Bignum32_mod" 

external _8_Hacl_Bignum32_mod_exp_vartime
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> _ CI.fatptr -> bool
  =
  "_8_Hacl_Bignum32_mod_exp_vartime_byte6" "_8_Hacl_Bignum32_mod_exp_vartime" 

external _9_Hacl_Bignum32_mod_exp_consttime
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> _ CI.fatptr -> bool
  =
  "_9_Hacl_Bignum32_mod_exp_consttime_byte6" "_9_Hacl_Bignum32_mod_exp_consttime"
  

external _10_Hacl_Bignum32_mod_inv_prime_vartime
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> bool
  = "_10_Hacl_Bignum32_mod_inv_prime_vartime" 

external _11_Hacl_Bignum32_mont_ctx_init
  : Unsigned.uint32 -> _ CI.fatptr -> CI.voidp
  = "_11_Hacl_Bignum32_mont_ctx_init" 

external _12_Hacl_Bignum32_mont_ctx_free : _ CI.fatptr -> unit
  = "_12_Hacl_Bignum32_mont_ctx_free" 

external _13_Hacl_Bignum32_mod_precomp
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_13_Hacl_Bignum32_mod_precomp" 

external _14_Hacl_Bignum32_mod_exp_vartime_precomp
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_14_Hacl_Bignum32_mod_exp_vartime_precomp" 

external _15_Hacl_Bignum32_mod_exp_consttime_precomp
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_15_Hacl_Bignum32_mod_exp_consttime_precomp" 

external _16_Hacl_Bignum32_mod_inv_prime_vartime_precomp
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_16_Hacl_Bignum32_mod_inv_prime_vartime_precomp" 

external _17_Hacl_Bignum32_new_bn_from_bytes_be
  : Unsigned.uint32 -> bytes CI.ocaml -> CI.voidp
  = "_17_Hacl_Bignum32_new_bn_from_bytes_be" 

external _18_Hacl_Bignum32_new_bn_from_bytes_le
  : Unsigned.uint32 -> bytes CI.ocaml -> CI.voidp
  = "_18_Hacl_Bignum32_new_bn_from_bytes_le" 

external _19_Hacl_Bignum32_bn_to_bytes_be
  : Unsigned.uint32 -> _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_19_Hacl_Bignum32_bn_to_bytes_be" 

external _20_Hacl_Bignum32_bn_to_bytes_le
  : Unsigned.uint32 -> _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_20_Hacl_Bignum32_bn_to_bytes_le" 

external _21_Hacl_Bignum32_lt_mask
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  = "_21_Hacl_Bignum32_lt_mask" 

external _22_Hacl_Bignum32_eq_mask
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  = "_22_Hacl_Bignum32_eq_mask" 

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
       (CI.Pointer _,
        Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_Bignum32_eq_mask" ->
  (fun x1 x2 x4 ->
    let CI.CPointer x5 = x4 in
    let CI.CPointer x3 = x2 in _22_Hacl_Bignum32_eq_mask x1 x3 x5)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_Bignum32_lt_mask" ->
  (fun x6 x7 x9 ->
    let CI.CPointer x10 = x9 in
    let CI.CPointer x8 = x7 in _21_Hacl_Bignum32_lt_mask x6 x8 x10)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Bignum32_bn_to_bytes_le" ->
  (fun x11 x12 x14 ->
    let CI.CPointer x13 = x12 in _20_Hacl_Bignum32_bn_to_bytes_le x11 x13 x14)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Bignum32_bn_to_bytes_be" ->
  (fun x15 x16 x18 ->
    let CI.CPointer x17 = x16 in _19_Hacl_Bignum32_bn_to_bytes_be x15 x17 x18)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Returns (CI.Pointer x21))),
  "Hacl_Bignum32_new_bn_from_bytes_le" ->
  (fun x19 x20 ->
    CI.make_ptr x21 (_18_Hacl_Bignum32_new_bn_from_bytes_le x19 x20))
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Returns (CI.Pointer x24))),
  "Hacl_Bignum32_new_bn_from_bytes_be" ->
  (fun x22 x23 ->
    CI.make_ptr x24 (_17_Hacl_Bignum32_new_bn_from_bytes_be x22 x23))
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum32_mod_inv_prime_vartime_precomp" ->
  (fun x25 x27 x29 ->
    let CI.CPointer x30 = x29 in
    let CI.CPointer x28 = x27 in
    let CI.CPointer x26 = x25 in
    _16_Hacl_Bignum32_mod_inv_prime_vartime_precomp x26 x28 x30)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum32_mod_exp_consttime_precomp" ->
  (fun x31 x33 x35 x36 x38 ->
    let CI.CPointer x39 = x38 in
    let CI.CPointer x37 = x36 in
    let CI.CPointer x34 = x33 in
    let CI.CPointer x32 = x31 in
    _15_Hacl_Bignum32_mod_exp_consttime_precomp x32 x34 x35 x37 x39)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum32_mod_exp_vartime_precomp" ->
  (fun x40 x42 x44 x45 x47 ->
    let CI.CPointer x48 = x47 in
    let CI.CPointer x46 = x45 in
    let CI.CPointer x43 = x42 in
    let CI.CPointer x41 = x40 in
    _14_Hacl_Bignum32_mod_exp_vartime_precomp x41 x43 x44 x46 x48)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum32_mod_precomp" ->
  (fun x49 x51 x53 ->
    let CI.CPointer x54 = x53 in
    let CI.CPointer x52 = x51 in
    let CI.CPointer x50 = x49 in _13_Hacl_Bignum32_mod_precomp x50 x52 x54)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Bignum32_mont_ctx_free" ->
  (fun x55 ->
    let CI.CPointer x56 = x55 in _12_Hacl_Bignum32_mont_ctx_free x56)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Returns (CI.Pointer x60))),
  "Hacl_Bignum32_mont_ctx_init" ->
  (fun x57 x58 ->
    let CI.CPointer x59 = x58 in
    CI.make_ptr x60 (_11_Hacl_Bignum32_mont_ctx_init x57 x59))
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))))),
  "Hacl_Bignum32_mod_inv_prime_vartime" ->
  (fun x61 x62 x64 x66 ->
    let CI.CPointer x67 = x66 in
    let CI.CPointer x65 = x64 in
    let CI.CPointer x63 = x62 in
    _10_Hacl_Bignum32_mod_inv_prime_vartime x61 x63 x65 x67)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))))))),
  "Hacl_Bignum32_mod_exp_consttime" ->
  (fun x68 x69 x71 x73 x74 x76 ->
    let CI.CPointer x77 = x76 in
    let CI.CPointer x75 = x74 in
    let CI.CPointer x72 = x71 in
    let CI.CPointer x70 = x69 in
    _9_Hacl_Bignum32_mod_exp_consttime x68 x70 x72 x73 x75 x77)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))))))),
  "Hacl_Bignum32_mod_exp_vartime" ->
  (fun x78 x79 x81 x83 x84 x86 ->
    let CI.CPointer x87 = x86 in
    let CI.CPointer x85 = x84 in
    let CI.CPointer x82 = x81 in
    let CI.CPointer x80 = x79 in
    _8_Hacl_Bignum32_mod_exp_vartime x78 x80 x82 x83 x85 x87)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Bool))))),
  "Hacl_Bignum32_mod" ->
  (fun x88 x89 x91 x93 ->
    let CI.CPointer x94 = x93 in
    let CI.CPointer x92 = x91 in
    let CI.CPointer x90 = x89 in _7_Hacl_Bignum32_mod x88 x90 x92 x94)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum32_sqr" ->
  (fun x95 x96 x98 ->
    let CI.CPointer x99 = x98 in
    let CI.CPointer x97 = x96 in _6_Hacl_Bignum32_sqr x95 x97 x99)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Bignum32_mul" ->
  (fun x100 x101 x103 x105 ->
    let CI.CPointer x106 = x105 in
    let CI.CPointer x104 = x103 in
    let CI.CPointer x102 = x101 in _5_Hacl_Bignum32_mul x100 x102 x104 x106)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum32_sub_mod" ->
  (fun x107 x108 x110 x112 x114 ->
    let CI.CPointer x115 = x114 in
    let CI.CPointer x113 = x112 in
    let CI.CPointer x111 = x110 in
    let CI.CPointer x109 = x108 in
    _4_Hacl_Bignum32_sub_mod x107 x109 x111 x113 x115)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum32_add_mod" ->
  (fun x116 x117 x119 x121 x123 ->
    let CI.CPointer x124 = x123 in
    let CI.CPointer x122 = x121 in
    let CI.CPointer x120 = x119 in
    let CI.CPointer x118 = x117 in
    _3_Hacl_Bignum32_add_mod x116 x118 x120 x122 x124)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))),
  "Hacl_Bignum32_sub" ->
  (fun x125 x126 x128 x130 ->
    let CI.CPointer x131 = x130 in
    let CI.CPointer x129 = x128 in
    let CI.CPointer x127 = x126 in _2_Hacl_Bignum32_sub x125 x127 x129 x131)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))),
  "Hacl_Bignum32_add" ->
  (fun x132 x133 x135 x137 ->
    let CI.CPointer x138 = x137 in
    let CI.CPointer x136 = x135 in
    let CI.CPointer x134 = x133 in _1_Hacl_Bignum32_add x132 x134 x136 x138)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
