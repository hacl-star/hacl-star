module CI = Cstubs_internals

external _1_EverCrypt_Hash_alg_of_state : _ CI.fatptr -> Unsigned.uint8
  = "_1_EverCrypt_Hash_alg_of_state" 

external _2_EverCrypt_Hash_create_in : Unsigned.uint8 -> CI.voidp
  = "_2_EverCrypt_Hash_create_in" 

external _3_EverCrypt_Hash_create : Unsigned.uint8 -> CI.voidp
  = "_3_EverCrypt_Hash_create" 

external _4_EverCrypt_Hash_init : _ CI.fatptr -> unit
  = "_4_EverCrypt_Hash_init" 

external _5_EverCrypt_Hash_update_multi_256
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_5_EverCrypt_Hash_update_multi_256" 

external _6_EverCrypt_Hash_update
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> unit
  = "_6_EverCrypt_Hash_update" 

external _7_EverCrypt_Hash_update_multi
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> Unsigned.uint32 ->
    unit = "_7_EverCrypt_Hash_update_multi" 

external _8_EverCrypt_Hash_update_last_256
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> Unsigned.uint32 ->
    unit = "_8_EverCrypt_Hash_update_last_256" 

external _9_EverCrypt_Hash_update_last
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> Unsigned.uint32 ->
    unit = "_9_EverCrypt_Hash_update_last" 

external _10_EverCrypt_Hash_finish : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_10_EverCrypt_Hash_finish" 

external _11_EverCrypt_Hash_free : _ CI.fatptr -> unit
  = "_11_EverCrypt_Hash_free" 

external _12_EverCrypt_Hash_copy : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_12_EverCrypt_Hash_copy" 

external _13_EverCrypt_Hash_hash_256
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_13_EverCrypt_Hash_hash_256" 

external _14_EverCrypt_Hash_hash_224
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_14_EverCrypt_Hash_hash_224" 

external _15_EverCrypt_Hash_hash
  : Unsigned.uint8 -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    unit = "_15_EverCrypt_Hash_hash" 

external _16_EverCrypt_Hash_Incremental_hash_len
  : Unsigned.uint8 -> Unsigned.uint32
  = "_16_EverCrypt_Hash_Incremental_hash_len" 

external _17_EverCrypt_Hash_Incremental_block_len
  : Unsigned.uint8 -> Unsigned.uint32
  = "_17_EverCrypt_Hash_Incremental_block_len" 

external _18_EverCrypt_Hash_Incremental_create_in
  : Unsigned.uint8 -> CI.voidp = "_18_EverCrypt_Hash_Incremental_create_in" 

external _19_EverCrypt_Hash_Incremental_init : _ CI.fatptr -> unit
  = "_19_EverCrypt_Hash_Incremental_init" 

external _20_EverCrypt_Hash_Incremental_max_input_len64
  : Unsigned.uint8 -> Unsigned.uint64
  = "_20_EverCrypt_Hash_Incremental_max_input_len64" 

external _21_EverCrypt_Hash_Incremental_update
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> Unsigned.uint8
  = "_21_EverCrypt_Hash_Incremental_update" 

external _22_EverCrypt_Hash_Incremental_finish_md5
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_22_EverCrypt_Hash_Incremental_finish_md5" 

external _23_EverCrypt_Hash_Incremental_finish_sha1
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_23_EverCrypt_Hash_Incremental_finish_sha1" 

external _24_EverCrypt_Hash_Incremental_finish_sha224
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_24_EverCrypt_Hash_Incremental_finish_sha224" 

external _25_EverCrypt_Hash_Incremental_finish_sha256
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_25_EverCrypt_Hash_Incremental_finish_sha256" 

external _26_EverCrypt_Hash_Incremental_finish_sha3_256
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_26_EverCrypt_Hash_Incremental_finish_sha3_256" 

external _27_EverCrypt_Hash_Incremental_finish_sha384
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_27_EverCrypt_Hash_Incremental_finish_sha384" 

external _28_EverCrypt_Hash_Incremental_finish_sha512
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_28_EverCrypt_Hash_Incremental_finish_sha512" 

external _29_EverCrypt_Hash_Incremental_finish_blake2s
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_29_EverCrypt_Hash_Incremental_finish_blake2s" 

external _30_EverCrypt_Hash_Incremental_finish_blake2b
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_30_EverCrypt_Hash_Incremental_finish_blake2b" 

external _31_EverCrypt_Hash_Incremental_alg_of_state
  : _ CI.fatptr -> Unsigned.uint8
  = "_31_EverCrypt_Hash_Incremental_alg_of_state" 

external _32_EverCrypt_Hash_Incremental_finish
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_32_EverCrypt_Hash_Incremental_finish" 

external _33_EverCrypt_Hash_Incremental_free : _ CI.fatptr -> unit
  = "_33_EverCrypt_Hash_Incremental_free" 

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
| Function (CI.Pointer _, Returns CI.Void), "EverCrypt_Hash_Incremental_free" ->
  (fun x1 ->
    let CI.CPointer x2 = x1 in _33_EverCrypt_Hash_Incremental_free x2)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish" ->
  (fun x3 x5 ->
    let CI.CPointer x4 = x3 in _32_EverCrypt_Hash_Incremental_finish x4 x5)
| Function
    (CI.Pointer _,
     Returns (CI.View {CI.ty = CI.Primitive CI.Uint8_t; read = x8; _})),
  "EverCrypt_Hash_Incremental_alg_of_state" ->
  (fun x6 ->
    let CI.CPointer x7 = x6 in
    x8 (_31_EverCrypt_Hash_Incremental_alg_of_state x7))
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_blake2b" ->
  (fun x9 x11 ->
    let CI.CPointer x10 = x9 in
    _30_EverCrypt_Hash_Incremental_finish_blake2b x10 x11)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_blake2s" ->
  (fun x12 x14 ->
    let CI.CPointer x13 = x12 in
    _29_EverCrypt_Hash_Incremental_finish_blake2s x13 x14)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_sha512" ->
  (fun x15 x17 ->
    let CI.CPointer x16 = x15 in
    _28_EverCrypt_Hash_Incremental_finish_sha512 x16 x17)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_sha384" ->
  (fun x18 x20 ->
    let CI.CPointer x19 = x18 in
    _27_EverCrypt_Hash_Incremental_finish_sha384 x19 x20)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_sha3_256" ->
  (fun x21 x23 ->
    let CI.CPointer x22 = x21 in
    _26_EverCrypt_Hash_Incremental_finish_sha3_256 x22 x23)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_sha256" ->
  (fun x24 x26 ->
    let CI.CPointer x25 = x24 in
    _25_EverCrypt_Hash_Incremental_finish_sha256 x25 x26)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_sha224" ->
  (fun x27 x29 ->
    let CI.CPointer x28 = x27 in
    _24_EverCrypt_Hash_Incremental_finish_sha224 x28 x29)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_sha1" ->
  (fun x30 x32 ->
    let CI.CPointer x31 = x30 in
    _23_EverCrypt_Hash_Incremental_finish_sha1 x31 x32)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_Incremental_finish_md5" ->
  (fun x33 x35 ->
    let CI.CPointer x34 = x33 in
    _22_EverCrypt_Hash_Incremental_finish_md5 x34 x35)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Returns (CI.View {CI.ty = CI.Primitive CI.Uint8_t; read = x40; _})))),
  "EverCrypt_Hash_Incremental_update" ->
  (fun x36 x38 x39 ->
    let CI.CPointer x37 = x36 in
    x40 (_21_EverCrypt_Hash_Incremental_update x37 x38 x39))
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x42; _},
     Returns (CI.Primitive CI.Uint64_t)),
  "EverCrypt_Hash_Incremental_max_input_len64" ->
  (fun x41 ->
    let x43 = x42 x41 in _20_EverCrypt_Hash_Incremental_max_input_len64 x43)
| Function (CI.Pointer _, Returns CI.Void), "EverCrypt_Hash_Incremental_init" ->
  (fun x44 ->
    let CI.CPointer x45 = x44 in _19_EverCrypt_Hash_Incremental_init x45)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x47; _},
     Returns (CI.Pointer x49)),
  "EverCrypt_Hash_Incremental_create_in" ->
  (fun x46 ->
    let x48 = x47 x46 in
    CI.make_ptr x49 (_18_EverCrypt_Hash_Incremental_create_in x48))
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x51; _},
     Returns (CI.Primitive CI.Uint32_t)),
  "EverCrypt_Hash_Incremental_block_len" ->
  (fun x50 ->
    let x52 = x51 x50 in _17_EverCrypt_Hash_Incremental_block_len x52)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x54; _},
     Returns (CI.Primitive CI.Uint32_t)),
  "EverCrypt_Hash_Incremental_hash_len" ->
  (fun x53 ->
    let x55 = x54 x53 in _16_EverCrypt_Hash_Incremental_hash_len x55)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x57; _},
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))),
  "EverCrypt_Hash_hash" ->
  (fun x56 x59 x60 x61 ->
    let x58 = x57 x56 in _15_EverCrypt_Hash_hash x58 x59 x60 x61)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "EverCrypt_Hash_hash_224" -> _14_EverCrypt_Hash_hash_224
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "EverCrypt_Hash_hash_256" -> _13_EverCrypt_Hash_hash_256
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "EverCrypt_Hash_copy" ->
  (fun x68 x70 ->
    let CI.CPointer x71 = x70 in
    let CI.CPointer x69 = x68 in _12_EverCrypt_Hash_copy x69 x71)
| Function (CI.Pointer _, Returns CI.Void), "EverCrypt_Hash_free" ->
  (fun x72 -> let CI.CPointer x73 = x72 in _11_EverCrypt_Hash_free x73)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "EverCrypt_Hash_finish" ->
  (fun x74 x76 ->
    let CI.CPointer x75 = x74 in _10_EverCrypt_Hash_finish x75 x76)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))),
  "EverCrypt_Hash_update_last" ->
  (fun x77 x79 x80 x81 ->
    let CI.CPointer x78 = x77 in
    _9_EverCrypt_Hash_update_last x78 x79 x80 x81)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))),
  "EverCrypt_Hash_update_last_256" ->
  (fun x82 x84 x85 x86 ->
    let CI.CPointer x83 = x82 in
    _8_EverCrypt_Hash_update_last_256 x83 x84 x85 x86)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))),
  "EverCrypt_Hash_update_multi" ->
  (fun x87 x89 x90 x91 ->
    let CI.CPointer x88 = x87 in
    _7_EverCrypt_Hash_update_multi x88 x89 x90 x91)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "EverCrypt_Hash_update" ->
  (fun x92 x94 x95 ->
    let CI.CPointer x93 = x92 in _6_EverCrypt_Hash_update x93 x94 x95)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "EverCrypt_Hash_update_multi_256" ->
  (fun x96 x98 x99 ->
    let CI.CPointer x97 = x96 in
    _5_EverCrypt_Hash_update_multi_256 x97 x98 x99)
| Function (CI.Pointer _, Returns CI.Void), "EverCrypt_Hash_init" ->
  (fun x100 -> let CI.CPointer x101 = x100 in _4_EverCrypt_Hash_init x101)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x103; _},
     Returns (CI.Pointer x105)),
  "EverCrypt_Hash_create" ->
  (fun x102 ->
    let x104 = x103 x102 in CI.make_ptr x105 (_3_EverCrypt_Hash_create x104))
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x107; _},
     Returns (CI.Pointer x109)),
  "EverCrypt_Hash_create_in" ->
  (fun x106 ->
    let x108 = x107 x106 in
    CI.make_ptr x109 (_2_EverCrypt_Hash_create_in x108))
| Function
    (CI.Pointer _,
     Returns (CI.View {CI.ty = CI.Primitive CI.Uint8_t; read = x112; _})),
  "EverCrypt_Hash_alg_of_state" ->
  (fun x110 ->
    let CI.CPointer x111 = x110 in x112 (_1_EverCrypt_Hash_alg_of_state x111))
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
