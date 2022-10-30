module CI = Cstubs_internals

external _1_Hacl_Bignum4096_add
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64
  = "_1_Hacl_Bignum4096_add" 

external _2_Hacl_Bignum4096_sub
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64
  = "_2_Hacl_Bignum4096_sub" 

external _3_Hacl_Bignum4096_add_mod
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_3_Hacl_Bignum4096_add_mod" 

external _4_Hacl_Bignum4096_sub_mod
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_4_Hacl_Bignum4096_sub_mod" 

external _5_Hacl_Bignum4096_mul
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_5_Hacl_Bignum4096_mul" 

external _6_Hacl_Bignum4096_sqr : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_6_Hacl_Bignum4096_sqr" 

external _7_Hacl_Bignum4096_mod
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> bool
  = "_7_Hacl_Bignum4096_mod" 

external _8_Hacl_Bignum4096_mod_exp_vartime
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> bool = "_8_Hacl_Bignum4096_mod_exp_vartime" 

external _9_Hacl_Bignum4096_mod_exp_consttime
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> bool = "_9_Hacl_Bignum4096_mod_exp_consttime" 

external _10_Hacl_Bignum4096_mod_inv_prime_vartime
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> bool
  = "_10_Hacl_Bignum4096_mod_inv_prime_vartime" 

external _11_Hacl_Bignum4096_mont_ctx_init : _ CI.fatptr -> CI.voidp
  = "_11_Hacl_Bignum4096_mont_ctx_init" 

external _12_Hacl_Bignum4096_mont_ctx_free : _ CI.fatptr -> unit
  = "_12_Hacl_Bignum4096_mont_ctx_free" 

external _13_Hacl_Bignum4096_mod_precomp
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_13_Hacl_Bignum4096_mod_precomp" 

external _14_Hacl_Bignum4096_mod_exp_vartime_precomp
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_14_Hacl_Bignum4096_mod_exp_vartime_precomp" 

external _15_Hacl_Bignum4096_mod_exp_consttime_precomp
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_15_Hacl_Bignum4096_mod_exp_consttime_precomp" 

external _16_Hacl_Bignum4096_mod_inv_prime_vartime_precomp
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_16_Hacl_Bignum4096_mod_inv_prime_vartime_precomp" 

external _17_Hacl_Bignum4096_new_bn_from_bytes_be
  : Unsigned.uint32 -> bytes CI.ocaml -> CI.voidp
  = "_17_Hacl_Bignum4096_new_bn_from_bytes_be" 

external _18_Hacl_Bignum4096_new_bn_from_bytes_le
  : Unsigned.uint32 -> bytes CI.ocaml -> CI.voidp
  = "_18_Hacl_Bignum4096_new_bn_from_bytes_le" 

external _19_Hacl_Bignum4096_bn_to_bytes_be
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_19_Hacl_Bignum4096_bn_to_bytes_be" 

external _20_Hacl_Bignum4096_bn_to_bytes_le
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_20_Hacl_Bignum4096_bn_to_bytes_le" 

external _21_Hacl_Bignum4096_lt_mask
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64
  = "_21_Hacl_Bignum4096_lt_mask" 

external _22_Hacl_Bignum4096_eq_mask
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64
  = "_22_Hacl_Bignum4096_eq_mask" 

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
     Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t))),
  "Hacl_Bignum4096_eq_mask" ->
  (fun x1 x3 ->
    let CI.CPointer x4 = x3 in
    let CI.CPointer x2 = x1 in _22_Hacl_Bignum4096_eq_mask x2 x4)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t))),
  "Hacl_Bignum4096_lt_mask" ->
  (fun x5 x7 ->
    let CI.CPointer x8 = x7 in
    let CI.CPointer x6 = x5 in _21_Hacl_Bignum4096_lt_mask x6 x8)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Bignum4096_bn_to_bytes_le" ->
  (fun x9 x11 ->
    let CI.CPointer x10 = x9 in _20_Hacl_Bignum4096_bn_to_bytes_le x10 x11)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Bignum4096_bn_to_bytes_be" ->
  (fun x12 x14 ->
    let CI.CPointer x13 = x12 in _19_Hacl_Bignum4096_bn_to_bytes_be x13 x14)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Returns (CI.Pointer x17))),
  "Hacl_Bignum4096_new_bn_from_bytes_le" ->
  (fun x15 x16 ->
    CI.make_ptr x17 (_18_Hacl_Bignum4096_new_bn_from_bytes_le x15 x16))
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Returns (CI.Pointer x20))),
  "Hacl_Bignum4096_new_bn_from_bytes_be" ->
  (fun x18 x19 ->
    CI.make_ptr x20 (_17_Hacl_Bignum4096_new_bn_from_bytes_be x18 x19))
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum4096_mod_inv_prime_vartime_precomp" ->
  (fun x21 x23 x25 ->
    let CI.CPointer x26 = x25 in
    let CI.CPointer x24 = x23 in
    let CI.CPointer x22 = x21 in
    _16_Hacl_Bignum4096_mod_inv_prime_vartime_precomp x22 x24 x26)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum4096_mod_exp_consttime_precomp" ->
  (fun x27 x29 x31 x32 x34 ->
    let CI.CPointer x35 = x34 in
    let CI.CPointer x33 = x32 in
    let CI.CPointer x30 = x29 in
    let CI.CPointer x28 = x27 in
    _15_Hacl_Bignum4096_mod_exp_consttime_precomp x28 x30 x31 x33 x35)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum4096_mod_exp_vartime_precomp" ->
  (fun x36 x38 x40 x41 x43 ->
    let CI.CPointer x44 = x43 in
    let CI.CPointer x42 = x41 in
    let CI.CPointer x39 = x38 in
    let CI.CPointer x37 = x36 in
    _14_Hacl_Bignum4096_mod_exp_vartime_precomp x37 x39 x40 x42 x44)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum4096_mod_precomp" ->
  (fun x45 x47 x49 ->
    let CI.CPointer x50 = x49 in
    let CI.CPointer x48 = x47 in
    let CI.CPointer x46 = x45 in _13_Hacl_Bignum4096_mod_precomp x46 x48 x50)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Bignum4096_mont_ctx_free" ->
  (fun x51 ->
    let CI.CPointer x52 = x51 in _12_Hacl_Bignum4096_mont_ctx_free x52)
| Function (CI.Pointer _, Returns (CI.Pointer x55)),
  "Hacl_Bignum4096_mont_ctx_init" ->
  (fun x53 ->
    let CI.CPointer x54 = x53 in
    CI.make_ptr x55 (_11_Hacl_Bignum4096_mont_ctx_init x54))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Returns (CI.Primitive CI.Bool)))),
  "Hacl_Bignum4096_mod_inv_prime_vartime" ->
  (fun x56 x58 x60 ->
    let CI.CPointer x61 = x60 in
    let CI.CPointer x59 = x58 in
    let CI.CPointer x57 = x56 in
    _10_Hacl_Bignum4096_mod_inv_prime_vartime x57 x59 x61)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Pointer _, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_Bignum4096_mod_exp_consttime" ->
  (fun x62 x64 x66 x67 x69 ->
    let CI.CPointer x70 = x69 in
    let CI.CPointer x68 = x67 in
    let CI.CPointer x65 = x64 in
    let CI.CPointer x63 = x62 in
    _9_Hacl_Bignum4096_mod_exp_consttime x63 x65 x66 x68 x70)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Pointer _, Returns (CI.Primitive CI.Bool)))))),
  "Hacl_Bignum4096_mod_exp_vartime" ->
  (fun x71 x73 x75 x76 x78 ->
    let CI.CPointer x79 = x78 in
    let CI.CPointer x77 = x76 in
    let CI.CPointer x74 = x73 in
    let CI.CPointer x72 = x71 in
    _8_Hacl_Bignum4096_mod_exp_vartime x72 x74 x75 x77 x79)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Returns (CI.Primitive CI.Bool)))),
  "Hacl_Bignum4096_mod" ->
  (fun x80 x82 x84 ->
    let CI.CPointer x85 = x84 in
    let CI.CPointer x83 = x82 in
    let CI.CPointer x81 = x80 in _7_Hacl_Bignum4096_mod x81 x83 x85)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Bignum4096_sqr" ->
  (fun x86 x88 ->
    let CI.CPointer x89 = x88 in
    let CI.CPointer x87 = x86 in _6_Hacl_Bignum4096_sqr x87 x89)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Bignum4096_mul" ->
  (fun x90 x92 x94 ->
    let CI.CPointer x95 = x94 in
    let CI.CPointer x93 = x92 in
    let CI.CPointer x91 = x90 in _5_Hacl_Bignum4096_mul x91 x93 x95)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Bignum4096_sub_mod" ->
  (fun x96 x98 x100 x102 ->
    let CI.CPointer x103 = x102 in
    let CI.CPointer x101 = x100 in
    let CI.CPointer x99 = x98 in
    let CI.CPointer x97 = x96 in _4_Hacl_Bignum4096_sub_mod x97 x99 x101 x103)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Bignum4096_add_mod" ->
  (fun x104 x106 x108 x110 ->
    let CI.CPointer x111 = x110 in
    let CI.CPointer x109 = x108 in
    let CI.CPointer x107 = x106 in
    let CI.CPointer x105 = x104 in
    _3_Hacl_Bignum4096_add_mod x105 x107 x109 x111)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t)))),
  "Hacl_Bignum4096_sub" ->
  (fun x112 x114 x116 ->
    let CI.CPointer x117 = x116 in
    let CI.CPointer x115 = x114 in
    let CI.CPointer x113 = x112 in _2_Hacl_Bignum4096_sub x113 x115 x117)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t)))),
  "Hacl_Bignum4096_add" ->
  (fun x118 x120 x122 ->
    let CI.CPointer x123 = x122 in
    let CI.CPointer x121 = x120 in
    let CI.CPointer x119 = x118 in _1_Hacl_Bignum4096_add x119 x121 x123)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
