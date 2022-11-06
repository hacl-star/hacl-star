module CI = Cstubs_internals

external _1_Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_1_Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32" 

external _2_Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_2_Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64" 

external _3_Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_3_Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32" 

external _4_Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_4_Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64" 

external _5_Hacl_Bignum_bn_add_mod_n_u32
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_5_Hacl_Bignum_bn_add_mod_n_u32" 

external _6_Hacl_Bignum_bn_add_mod_n_u64
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_6_Hacl_Bignum_bn_add_mod_n_u64" 

external _7_Hacl_Bignum_bn_sub_mod_n_u32
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_7_Hacl_Bignum_bn_sub_mod_n_u32" 

external _8_Hacl_Bignum_bn_sub_mod_n_u64
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_8_Hacl_Bignum_bn_sub_mod_n_u64" 

external _9_Hacl_Bignum_ModInvLimb_mod_inv_uint32
  : Unsigned.uint32 -> Unsigned.uint32
  = "_9_Hacl_Bignum_ModInvLimb_mod_inv_uint32" 

external _10_Hacl_Bignum_ModInvLimb_mod_inv_uint64
  : Unsigned.uint64 -> Unsigned.uint64
  = "_10_Hacl_Bignum_ModInvLimb_mod_inv_uint64" 

external _11_Hacl_Bignum_Montgomery_bn_check_modulus_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32
  = "_11_Hacl_Bignum_Montgomery_bn_check_modulus_u32" 

external _12_Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_12_Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32" 

external _13_Hacl_Bignum_Montgomery_bn_mont_reduction_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_13_Hacl_Bignum_Montgomery_bn_mont_reduction_u32" 

external _14_Hacl_Bignum_Montgomery_bn_to_mont_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_14_Hacl_Bignum_Montgomery_bn_to_mont_u32_byte6" "_14_Hacl_Bignum_Montgomery_bn_to_mont_u32"
  

external _15_Hacl_Bignum_Montgomery_bn_from_mont_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_15_Hacl_Bignum_Montgomery_bn_from_mont_u32" 

external _16_Hacl_Bignum_Montgomery_bn_mont_mul_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_16_Hacl_Bignum_Montgomery_bn_mont_mul_u32_byte6" "_16_Hacl_Bignum_Montgomery_bn_mont_mul_u32"
  

external _17_Hacl_Bignum_Montgomery_bn_mont_sqr_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_17_Hacl_Bignum_Montgomery_bn_mont_sqr_u32" 

external _18_Hacl_Bignum_Montgomery_bn_check_modulus_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64
  = "_18_Hacl_Bignum_Montgomery_bn_check_modulus_u64" 

external _19_Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_19_Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64" 

external _20_Hacl_Bignum_Montgomery_bn_mont_reduction_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_20_Hacl_Bignum_Montgomery_bn_mont_reduction_u64" 

external _21_Hacl_Bignum_Montgomery_bn_to_mont_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64 -> _ CI.fatptr ->
    _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_21_Hacl_Bignum_Montgomery_bn_to_mont_u64_byte6" "_21_Hacl_Bignum_Montgomery_bn_to_mont_u64"
  

external _22_Hacl_Bignum_Montgomery_bn_from_mont_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_22_Hacl_Bignum_Montgomery_bn_from_mont_u64" 

external _23_Hacl_Bignum_Montgomery_bn_mont_mul_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64 -> _ CI.fatptr ->
    _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_23_Hacl_Bignum_Montgomery_bn_mont_mul_u64_byte6" "_23_Hacl_Bignum_Montgomery_bn_mont_mul_u64"
  

external _24_Hacl_Bignum_Montgomery_bn_mont_sqr_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64 -> _ CI.fatptr ->
    _ CI.fatptr -> unit = "_24_Hacl_Bignum_Montgomery_bn_mont_sqr_u64" 

external _25_Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> Unsigned.uint32
  = "_25_Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32" 

external _26_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_26_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32_byte8" 
  "_26_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32" 

external _27_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_27_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32_byte8" 
  "_27_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32" 

external _28_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_28_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32_byte7" "_28_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32"
  

external _29_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_29_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32_byte7" "_29_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32"
  

external _30_Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> Unsigned.uint64
  = "_30_Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64" 

external _31_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64 -> _ CI.fatptr ->
    _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_31_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64_byte8" 
  "_31_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64" 

external _32_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64
  : Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint64 -> _ CI.fatptr ->
    _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_32_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64_byte8" 
  "_32_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64" 

external _33_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_33_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64_byte7" "_33_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64"
  

external _34_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64
  : Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr ->
    Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> unit
  =
  "_34_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64_byte7" "_34_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64"
  

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
          (CI.Pointer _,
           Function
             (CI.Pointer _,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))))),
  "Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64" ->
  (fun x1 x2 x3 x5 x7 x8 x10 ->
    let CI.CPointer x11 = x10 in
    let CI.CPointer x9 = x8 in
    let CI.CPointer x6 = x5 in
    let CI.CPointer x4 = x3 in
    _34_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64 x1 x2 x4 x6 x7 x9
    x11)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Pointer _,
           Function
             (CI.Pointer _,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))))),
  "Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64" ->
  (fun x12 x13 x14 x16 x18 x19 x21 ->
    let CI.CPointer x22 = x21 in
    let CI.CPointer x20 = x19 in
    let CI.CPointer x17 = x16 in
    let CI.CPointer x15 = x14 in
    _33_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64 x12 x13 x15 x17 x18
    x20 x22)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint64_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function
                      (CI.Pointer _,
                       Function (CI.Pointer _, Returns CI.Void)))))))),
  "Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64" ->
  (fun x23 x24 x26 x27 x29 x31 x32 x34 ->
    let CI.CPointer x35 = x34 in
    let CI.CPointer x33 = x32 in
    let CI.CPointer x30 = x29 in
    let CI.CPointer x28 = x27 in
    let CI.CPointer x25 = x24 in
    _32_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64 x23 x25
    x26 x28 x30 x31 x33 x35)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint64_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function
                      (CI.Pointer _,
                       Function (CI.Pointer _, Returns CI.Void)))))))),
  "Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64" ->
  (fun x36 x37 x39 x40 x42 x44 x45 x47 ->
    let CI.CPointer x48 = x47 in
    let CI.CPointer x46 = x45 in
    let CI.CPointer x43 = x42 in
    let CI.CPointer x41 = x40 in
    let CI.CPointer x38 = x37 in
    _31_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64 x36 x38 x39
    x41 x43 x44 x46 x48)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t)))))),
  "Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64" ->
  (fun x49 x50 x52 x54 x55 ->
    let CI.CPointer x56 = x55 in
    let CI.CPointer x53 = x52 in
    let CI.CPointer x51 = x50 in
    _30_Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64 x49 x51 x53 x54 x56)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Pointer _,
           Function
             (CI.Pointer _,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))))),
  "Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32" ->
  (fun x57 x58 x59 x61 x63 x64 x66 ->
    let CI.CPointer x67 = x66 in
    let CI.CPointer x65 = x64 in
    let CI.CPointer x62 = x61 in
    let CI.CPointer x60 = x59 in
    _29_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32 x57 x58 x60 x62
    x63 x65 x67)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Pointer _,
           Function
             (CI.Pointer _,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))))),
  "Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32" ->
  (fun x68 x69 x70 x72 x74 x75 x77 ->
    let CI.CPointer x78 = x77 in
    let CI.CPointer x76 = x75 in
    let CI.CPointer x73 = x72 in
    let CI.CPointer x71 = x70 in
    _28_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32 x68 x69 x71 x73 x74
    x76 x78)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function
                      (CI.Pointer _,
                       Function (CI.Pointer _, Returns CI.Void)))))))),
  "Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32" ->
  (fun x79 x80 x82 x83 x85 x87 x88 x90 ->
    let CI.CPointer x91 = x90 in
    let CI.CPointer x89 = x88 in
    let CI.CPointer x86 = x85 in
    let CI.CPointer x84 = x83 in
    let CI.CPointer x81 = x80 in
    _27_Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32 x79 x81
    x82 x84 x86 x87 x89 x91)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function
                      (CI.Pointer _,
                       Function (CI.Pointer _, Returns CI.Void)))))))),
  "Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32" ->
  (fun x92 x93 x95 x96 x98 x100 x101 x103 ->
    let CI.CPointer x104 = x103 in
    let CI.CPointer x102 = x101 in
    let CI.CPointer x99 = x98 in
    let CI.CPointer x97 = x96 in
    let CI.CPointer x94 = x93 in
    _26_Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32 x92 x94 x95
    x97 x99 x100 x102 x104)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32" ->
  (fun x105 x106 x108 x110 x111 ->
    let CI.CPointer x112 = x111 in
    let CI.CPointer x109 = x108 in
    let CI.CPointer x107 = x106 in
    _25_Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32 x105 x107 x109 x110
    x112)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint64_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Montgomery_bn_mont_sqr_u64" ->
  (fun x113 x114 x116 x117 x119 ->
    let CI.CPointer x120 = x119 in
    let CI.CPointer x118 = x117 in
    let CI.CPointer x115 = x114 in
    _24_Hacl_Bignum_Montgomery_bn_mont_sqr_u64 x113 x115 x116 x118 x120)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint64_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))))),
  "Hacl_Bignum_Montgomery_bn_mont_mul_u64" ->
  (fun x121 x122 x124 x125 x127 x129 ->
    let CI.CPointer x130 = x129 in
    let CI.CPointer x128 = x127 in
    let CI.CPointer x126 = x125 in
    let CI.CPointer x123 = x122 in
    _23_Hacl_Bignum_Montgomery_bn_mont_mul_u64 x121 x123 x124 x126 x128 x130)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint64_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Montgomery_bn_from_mont_u64" ->
  (fun x131 x132 x134 x135 x137 ->
    let CI.CPointer x138 = x137 in
    let CI.CPointer x136 = x135 in
    let CI.CPointer x133 = x132 in
    _22_Hacl_Bignum_Montgomery_bn_from_mont_u64 x131 x133 x134 x136 x138)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint64_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))))),
  "Hacl_Bignum_Montgomery_bn_to_mont_u64" ->
  (fun x139 x140 x142 x143 x145 x147 ->
    let CI.CPointer x148 = x147 in
    let CI.CPointer x146 = x145 in
    let CI.CPointer x144 = x143 in
    let CI.CPointer x141 = x140 in
    _21_Hacl_Bignum_Montgomery_bn_to_mont_u64 x139 x141 x142 x144 x146 x148)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint64_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Montgomery_bn_mont_reduction_u64" ->
  (fun x149 x150 x152 x153 x155 ->
    let CI.CPointer x156 = x155 in
    let CI.CPointer x154 = x153 in
    let CI.CPointer x151 = x150 in
    _20_Hacl_Bignum_Montgomery_bn_mont_reduction_u64 x149 x151 x152 x154 x156)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64" ->
  (fun x157 x158 x159 x161 ->
    let CI.CPointer x162 = x161 in
    let CI.CPointer x160 = x159 in
    _19_Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64 x157 x158 x160 x162)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t))),
  "Hacl_Bignum_Montgomery_bn_check_modulus_u64" ->
  (fun x163 x164 ->
    let CI.CPointer x165 = x164 in
    _18_Hacl_Bignum_Montgomery_bn_check_modulus_u64 x163 x165)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Montgomery_bn_mont_sqr_u32" ->
  (fun x166 x167 x169 x170 x172 ->
    let CI.CPointer x173 = x172 in
    let CI.CPointer x171 = x170 in
    let CI.CPointer x168 = x167 in
    _17_Hacl_Bignum_Montgomery_bn_mont_sqr_u32 x166 x168 x169 x171 x173)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))))),
  "Hacl_Bignum_Montgomery_bn_mont_mul_u32" ->
  (fun x174 x175 x177 x178 x180 x182 ->
    let CI.CPointer x183 = x182 in
    let CI.CPointer x181 = x180 in
    let CI.CPointer x179 = x178 in
    let CI.CPointer x176 = x175 in
    _16_Hacl_Bignum_Montgomery_bn_mont_mul_u32 x174 x176 x177 x179 x181 x183)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Montgomery_bn_from_mont_u32" ->
  (fun x184 x185 x187 x188 x190 ->
    let CI.CPointer x191 = x190 in
    let CI.CPointer x189 = x188 in
    let CI.CPointer x186 = x185 in
    _15_Hacl_Bignum_Montgomery_bn_from_mont_u32 x184 x186 x187 x189 x191)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))))),
  "Hacl_Bignum_Montgomery_bn_to_mont_u32" ->
  (fun x192 x193 x195 x196 x198 x200 ->
    let CI.CPointer x201 = x200 in
    let CI.CPointer x199 = x198 in
    let CI.CPointer x197 = x196 in
    let CI.CPointer x194 = x193 in
    _14_Hacl_Bignum_Montgomery_bn_to_mont_u32 x192 x194 x195 x197 x199 x201)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Montgomery_bn_mont_reduction_u32" ->
  (fun x202 x203 x205 x206 x208 ->
    let CI.CPointer x209 = x208 in
    let CI.CPointer x207 = x206 in
    let CI.CPointer x204 = x203 in
    _13_Hacl_Bignum_Montgomery_bn_mont_reduction_u32 x202 x204 x205 x207 x209)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32" ->
  (fun x210 x211 x212 x214 ->
    let CI.CPointer x215 = x214 in
    let CI.CPointer x213 = x212 in
    _12_Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32 x210 x211 x213 x215)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))),
  "Hacl_Bignum_Montgomery_bn_check_modulus_u32" ->
  (fun x216 x217 ->
    let CI.CPointer x218 = x217 in
    _11_Hacl_Bignum_Montgomery_bn_check_modulus_u32 x216 x218)
| Function (CI.Primitive CI.Uint64_t, Returns (CI.Primitive CI.Uint64_t)),
  "Hacl_Bignum_ModInvLimb_mod_inv_uint64" ->
  _10_Hacl_Bignum_ModInvLimb_mod_inv_uint64
| Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Uint32_t)),
  "Hacl_Bignum_ModInvLimb_mod_inv_uint32" ->
  _9_Hacl_Bignum_ModInvLimb_mod_inv_uint32
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_bn_sub_mod_n_u64" ->
  (fun x221 x222 x224 x226 x228 ->
    let CI.CPointer x229 = x228 in
    let CI.CPointer x227 = x226 in
    let CI.CPointer x225 = x224 in
    let CI.CPointer x223 = x222 in
    _8_Hacl_Bignum_bn_sub_mod_n_u64 x221 x223 x225 x227 x229)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_bn_sub_mod_n_u32" ->
  (fun x230 x231 x233 x235 x237 ->
    let CI.CPointer x238 = x237 in
    let CI.CPointer x236 = x235 in
    let CI.CPointer x234 = x233 in
    let CI.CPointer x232 = x231 in
    _7_Hacl_Bignum_bn_sub_mod_n_u32 x230 x232 x234 x236 x238)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_bn_add_mod_n_u64" ->
  (fun x239 x240 x242 x244 x246 ->
    let CI.CPointer x247 = x246 in
    let CI.CPointer x245 = x244 in
    let CI.CPointer x243 = x242 in
    let CI.CPointer x241 = x240 in
    _6_Hacl_Bignum_bn_add_mod_n_u64 x239 x241 x243 x245 x247)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_bn_add_mod_n_u32" ->
  (fun x248 x249 x251 x253 x255 ->
    let CI.CPointer x256 = x255 in
    let CI.CPointer x254 = x253 in
    let CI.CPointer x252 = x251 in
    let CI.CPointer x250 = x249 in
    _5_Hacl_Bignum_bn_add_mod_n_u32 x248 x250 x252 x254 x256)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64" ->
  (fun x257 x258 x260 x262 ->
    let CI.CPointer x263 = x262 in
    let CI.CPointer x261 = x260 in
    let CI.CPointer x259 = x258 in
    _4_Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64 x257 x259 x261 x263)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)))),
  "Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32" ->
  (fun x264 x265 x267 x269 ->
    let CI.CPointer x270 = x269 in
    let CI.CPointer x268 = x267 in
    let CI.CPointer x266 = x265 in
    _3_Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32 x264 x266 x268 x270)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64" ->
  (fun x271 x272 x274 x276 x278 ->
    let CI.CPointer x279 = x278 in
    let CI.CPointer x277 = x276 in
    let CI.CPointer x275 = x274 in
    let CI.CPointer x273 = x272 in
    _2_Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64 x271 x273 x275 x277 x279)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))))),
  "Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32" ->
  (fun x280 x281 x283 x285 x287 ->
    let CI.CPointer x288 = x287 in
    let CI.CPointer x286 = x285 in
    let CI.CPointer x284 = x283 in
    let CI.CPointer x282 = x281 in
    _1_Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32 x280 x282 x284 x286 x288)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
