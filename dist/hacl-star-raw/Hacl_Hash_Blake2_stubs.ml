module CI = Cstubs_internals

external _1_Hacl_Hash_Core_Blake2_init_blake2s_32
  : _ CI.fatptr -> Unsigned.uint64
  = "_1_Hacl_Hash_Core_Blake2_init_blake2s_32" 

external _2_Hacl_Hash_Core_Blake2_update_blake2s_32
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> Unsigned.uint64
  = "_2_Hacl_Hash_Core_Blake2_update_blake2s_32" 

external _3_Hacl_Hash_Core_Blake2_finish_blake2s_32
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> unit
  = "_3_Hacl_Hash_Core_Blake2_finish_blake2s_32" 

external _4_Hacl_Hash_Blake2_update_multi_blake2s_32
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> Unsigned.uint32 ->
    Unsigned.uint64 = "_4_Hacl_Hash_Blake2_update_multi_blake2s_32" 

external _5_Hacl_Hash_Blake2_update_last_blake2s_32
  : _ CI.fatptr -> Unsigned.uint64 -> Unsigned.uint64 -> bytes CI.ocaml ->
    Unsigned.uint32 -> Unsigned.uint64
  = "_5_Hacl_Hash_Blake2_update_last_blake2s_32" 

external _6_Hacl_Hash_Blake2_hash_blake2s_32
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_6_Hacl_Hash_Blake2_hash_blake2s_32" 

external _7_Hacl_Hash_Blake2_hash_blake2b_32
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_7_Hacl_Hash_Blake2_hash_blake2b_32" 

external _8_Hacl_Blake2b_32_blake2b_init
  : _ CI.fatptr -> Unsigned.uint32 -> Unsigned.uint32 -> unit
  = "_8_Hacl_Blake2b_32_blake2b_init" 

external _9_Hacl_Blake2b_32_blake2b_update_key
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_9_Hacl_Blake2b_32_blake2b_update_key" 

external _10_Hacl_Blake2b_32_blake2b_finish
  : Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_10_Hacl_Blake2b_32_blake2b_finish" 

external _11_Hacl_Blake2b_32_blake2b
  : Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_11_Hacl_Blake2b_32_blake2b_byte6" "_11_Hacl_Blake2b_32_blake2b" 

external _12_Hacl_Blake2s_32_blake2s_init
  : _ CI.fatptr -> Unsigned.uint32 -> Unsigned.uint32 -> unit
  = "_12_Hacl_Blake2s_32_blake2s_init" 

external _13_Hacl_Blake2s_32_blake2s_update_key
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> unit = "_13_Hacl_Blake2s_32_blake2s_update_key" 

external _14_Hacl_Blake2s_32_blake2s_update_multi
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64 ->
    bytes CI.ocaml -> Unsigned.uint32 -> unit
  =
  "_14_Hacl_Blake2s_32_blake2s_update_multi_byte6" "_14_Hacl_Blake2s_32_blake2s_update_multi"
  

external _15_Hacl_Blake2s_32_blake2s_update_last
  : Unsigned.uint32 -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64 ->
    Unsigned.uint32 -> bytes CI.ocaml -> unit
  =
  "_15_Hacl_Blake2s_32_blake2s_update_last_byte6" "_15_Hacl_Blake2s_32_blake2s_update_last"
  

external _16_Hacl_Blake2s_32_blake2s_finish
  : Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_16_Hacl_Blake2s_32_blake2s_finish" 

external _17_Hacl_Blake2s_32_blake2s
  : Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_17_Hacl_Blake2s_32_blake2s_byte6" "_17_Hacl_Blake2s_32_blake2s" 

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
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function (CI.OCaml CI.Bytes, Returns CI.Void)))))),
  "Hacl_Blake2s_32_blake2s" -> _17_Hacl_Blake2s_32_blake2s
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Blake2s_32_blake2s_finish" ->
  (fun x7 x8 x9 ->
    let CI.CPointer x10 = x9 in _16_Hacl_Blake2s_32_blake2s_finish x7 x8 x10)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint64_t,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function (CI.OCaml CI.Bytes, Returns CI.Void)))))),
  "Hacl_Blake2s_32_blake2s_update_last" ->
  (fun x11 x12 x14 x16 x17 x18 ->
    let CI.CPointer x15 = x14 in
    let CI.CPointer x13 = x12 in
    _15_Hacl_Blake2s_32_blake2s_update_last x11 x13 x15 x16 x17 x18)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint64_t,
              Function
                (CI.OCaml CI.Bytes,
                 Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))))),
  "Hacl_Blake2s_32_blake2s_update_multi" ->
  (fun x19 x20 x22 x24 x25 x26 ->
    let CI.CPointer x23 = x22 in
    let CI.CPointer x21 = x20 in
    _14_Hacl_Blake2s_32_blake2s_update_multi x19 x21 x23 x24 x25 x26)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "Hacl_Blake2s_32_blake2s_update_key" ->
  (fun x27 x29 x31 x32 x33 ->
    let CI.CPointer x30 = x29 in
    let CI.CPointer x28 = x27 in
    _13_Hacl_Blake2s_32_blake2s_update_key x28 x30 x31 x32 x33)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Blake2s_32_blake2s_init" ->
  (fun x34 x36 x37 ->
    let CI.CPointer x35 = x34 in _12_Hacl_Blake2s_32_blake2s_init x35 x36 x37)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function (CI.OCaml CI.Bytes, Returns CI.Void)))))),
  "Hacl_Blake2b_32_blake2b" -> _11_Hacl_Blake2b_32_blake2b
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Blake2b_32_blake2b_finish" ->
  (fun x44 x45 x46 ->
    let CI.CPointer x47 = x46 in
    _10_Hacl_Blake2b_32_blake2b_finish x44 x45 x47)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint32_t, Returns CI.Void))))),
  "Hacl_Blake2b_32_blake2b_update_key" ->
  (fun x48 x50 x52 x53 x54 ->
    let CI.CPointer x51 = x50 in
    let CI.CPointer x49 = x48 in
    _9_Hacl_Blake2b_32_blake2b_update_key x49 x51 x52 x53 x54)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Blake2b_32_blake2b_init" ->
  (fun x55 x57 x58 ->
    let CI.CPointer x56 = x55 in _8_Hacl_Blake2b_32_blake2b_init x56 x57 x58)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Hash_Blake2_hash_blake2b_32" -> _7_Hacl_Hash_Blake2_hash_blake2b_32
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Hash_Blake2_hash_blake2s_32" -> _6_Hacl_Hash_Blake2_hash_blake2s_32
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.Primitive CI.Uint64_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t,
                 Returns (CI.Primitive CI.Uint64_t)))))),
  "Hacl_Hash_Blake2_update_last_blake2s_32" ->
  (fun x65 x67 x68 x69 x70 ->
    let CI.CPointer x66 = x65 in
    _5_Hacl_Hash_Blake2_update_last_blake2s_32 x66 x67 x68 x69 x70)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Uint64_t))))),
  "Hacl_Hash_Blake2_update_multi_blake2s_32" ->
  (fun x71 x73 x74 x75 ->
    let CI.CPointer x72 = x71 in
    _4_Hacl_Hash_Blake2_update_multi_blake2s_32 x72 x73 x74 x75)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Hash_Core_Blake2_finish_blake2s_32" ->
  (fun x76 x78 x79 ->
    let CI.CPointer x77 = x76 in
    _3_Hacl_Hash_Core_Blake2_finish_blake2s_32 x77 x78 x79)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint64_t)))),
  "Hacl_Hash_Core_Blake2_update_blake2s_32" ->
  (fun x80 x82 x83 ->
    let CI.CPointer x81 = x80 in
    _2_Hacl_Hash_Core_Blake2_update_blake2s_32 x81 x82 x83)
| Function (CI.Pointer _, Returns (CI.Primitive CI.Uint64_t)),
  "Hacl_Hash_Core_Blake2_init_blake2s_32" ->
  (fun x84 ->
    let CI.CPointer x85 = x84 in _1_Hacl_Hash_Core_Blake2_init_blake2s_32 x85)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
