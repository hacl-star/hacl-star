module CI = Cstubs_internals

external _1_EverCrypt_DRBG_reseed_interval : unit -> CI.voidp
  = "_1_EverCrypt_DRBG_reseed_interval" 

external _2_EverCrypt_DRBG_max_output_length : unit -> CI.voidp
  = "_2_EverCrypt_DRBG_max_output_length" 

external _3_EverCrypt_DRBG_max_length : unit -> CI.voidp
  = "_3_EverCrypt_DRBG_max_length" 

external _4_EverCrypt_DRBG_max_personalization_string_length
  : unit -> CI.voidp = "_4_EverCrypt_DRBG_max_personalization_string_length" 

external _5_EverCrypt_DRBG_max_additional_input_length : unit -> CI.voidp
  = "_5_EverCrypt_DRBG_max_additional_input_length" 

external _6_EverCrypt_DRBG_min_length : Unsigned.uint8 -> Unsigned.uint32
  = "_6_EverCrypt_DRBG_min_length" 

external _7_EverCrypt_DRBG_create : Unsigned.uint8 -> CI.voidp
  = "_7_EverCrypt_DRBG_create" 

external _8_EverCrypt_DRBG_instantiate_sha1
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_8_EverCrypt_DRBG_instantiate_sha1" 

external _9_EverCrypt_DRBG_instantiate_sha2_256
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_9_EverCrypt_DRBG_instantiate_sha2_256" 

external _10_EverCrypt_DRBG_instantiate_sha2_384
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_10_EverCrypt_DRBG_instantiate_sha2_384" 

external _11_EverCrypt_DRBG_instantiate_sha2_512
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_11_EverCrypt_DRBG_instantiate_sha2_512" 

external _12_EverCrypt_DRBG_reseed_sha1
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_12_EverCrypt_DRBG_reseed_sha1" 

external _13_EverCrypt_DRBG_reseed_sha2_256
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_13_EverCrypt_DRBG_reseed_sha2_256" 

external _14_EverCrypt_DRBG_reseed_sha2_384
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_14_EverCrypt_DRBG_reseed_sha2_384" 

external _15_EverCrypt_DRBG_reseed_sha2_512
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_15_EverCrypt_DRBG_reseed_sha2_512" 

external _16_EverCrypt_DRBG_generate_sha1
  : bytes CI.ocaml -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bool = "_16_EverCrypt_DRBG_generate_sha1" 

external _17_EverCrypt_DRBG_generate_sha2_256
  : bytes CI.ocaml -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bool = "_17_EverCrypt_DRBG_generate_sha2_256" 

external _18_EverCrypt_DRBG_generate_sha2_384
  : bytes CI.ocaml -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bool = "_18_EverCrypt_DRBG_generate_sha2_384" 

external _19_EverCrypt_DRBG_generate_sha2_512
  : bytes CI.ocaml -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bool = "_19_EverCrypt_DRBG_generate_sha2_512" 

external _20_EverCrypt_DRBG_uninstantiate_sha1 : _ CI.fatptr -> unit
  = "_20_EverCrypt_DRBG_uninstantiate_sha1" 

external _21_EverCrypt_DRBG_uninstantiate_sha2_256 : _ CI.fatptr -> unit
  = "_21_EverCrypt_DRBG_uninstantiate_sha2_256" 

external _22_EverCrypt_DRBG_uninstantiate_sha2_384 : _ CI.fatptr -> unit
  = "_22_EverCrypt_DRBG_uninstantiate_sha2_384" 

external _23_EverCrypt_DRBG_uninstantiate_sha2_512 : _ CI.fatptr -> unit
  = "_23_EverCrypt_DRBG_uninstantiate_sha2_512" 

external _24_EverCrypt_DRBG_instantiate
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_24_EverCrypt_DRBG_instantiate" 

external _25_EverCrypt_DRBG_reseed
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> bool
  = "_25_EverCrypt_DRBG_reseed" 

external _26_EverCrypt_DRBG_generate
  : bytes CI.ocaml -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bool = "_26_EverCrypt_DRBG_generate" 

external _27_EverCrypt_DRBG_uninstantiate : _ CI.fatptr -> unit
  = "_27_EverCrypt_DRBG_uninstantiate" 

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
| Function (CI.Pointer _, Returns CI.Void), "EverCrypt_DRBG_uninstantiate" ->
  (fun x1 -> let CI.CPointer x2 = x1 in _27_EverCrypt_DRBG_uninstantiate x2)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))))),
  "EverCrypt_DRBG_generate" ->
  (fun x3 x4 x6 x7 x8 ->
    let CI.CPointer x5 = x4 in _26_EverCrypt_DRBG_generate x3 x5 x6 x7 x8)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_reseed" ->
  (fun x9 x11 x12 ->
    let CI.CPointer x10 = x9 in _25_EverCrypt_DRBG_reseed x10 x11 x12)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_instantiate" ->
  (fun x13 x15 x16 ->
    let CI.CPointer x14 = x13 in _24_EverCrypt_DRBG_instantiate x14 x15 x16)
| Function (CI.Pointer _, Returns CI.Void),
  "EverCrypt_DRBG_uninstantiate_sha2_512" ->
  (fun x17 ->
    let CI.CPointer x18 = x17 in
    _23_EverCrypt_DRBG_uninstantiate_sha2_512 x18)
| Function (CI.Pointer _, Returns CI.Void),
  "EverCrypt_DRBG_uninstantiate_sha2_384" ->
  (fun x19 ->
    let CI.CPointer x20 = x19 in
    _22_EverCrypt_DRBG_uninstantiate_sha2_384 x20)
| Function (CI.Pointer _, Returns CI.Void),
  "EverCrypt_DRBG_uninstantiate_sha2_256" ->
  (fun x21 ->
    let CI.CPointer x22 = x21 in
    _21_EverCrypt_DRBG_uninstantiate_sha2_256 x22)
| Function (CI.Pointer _, Returns CI.Void),
  "EverCrypt_DRBG_uninstantiate_sha1" ->
  (fun x23 ->
    let CI.CPointer x24 = x23 in _20_EverCrypt_DRBG_uninstantiate_sha1 x24)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))))),
  "EverCrypt_DRBG_generate_sha2_512" ->
  (fun x25 x26 x28 x29 x30 ->
    let CI.CPointer x27 = x26 in
    _19_EverCrypt_DRBG_generate_sha2_512 x25 x27 x28 x29 x30)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))))),
  "EverCrypt_DRBG_generate_sha2_384" ->
  (fun x31 x32 x34 x35 x36 ->
    let CI.CPointer x33 = x32 in
    _18_EverCrypt_DRBG_generate_sha2_384 x31 x33 x34 x35 x36)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))))),
  "EverCrypt_DRBG_generate_sha2_256" ->
  (fun x37 x38 x40 x41 x42 ->
    let CI.CPointer x39 = x38 in
    _17_EverCrypt_DRBG_generate_sha2_256 x37 x39 x40 x41 x42)
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))))),
  "EverCrypt_DRBG_generate_sha1" ->
  (fun x43 x44 x46 x47 x48 ->
    let CI.CPointer x45 = x44 in
    _16_EverCrypt_DRBG_generate_sha1 x43 x45 x46 x47 x48)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_reseed_sha2_512" ->
  (fun x49 x51 x52 ->
    let CI.CPointer x50 = x49 in
    _15_EverCrypt_DRBG_reseed_sha2_512 x50 x51 x52)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_reseed_sha2_384" ->
  (fun x53 x55 x56 ->
    let CI.CPointer x54 = x53 in
    _14_EverCrypt_DRBG_reseed_sha2_384 x54 x55 x56)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_reseed_sha2_256" ->
  (fun x57 x59 x60 ->
    let CI.CPointer x58 = x57 in
    _13_EverCrypt_DRBG_reseed_sha2_256 x58 x59 x60)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_reseed_sha1" ->
  (fun x61 x63 x64 ->
    let CI.CPointer x62 = x61 in _12_EverCrypt_DRBG_reseed_sha1 x62 x63 x64)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_instantiate_sha2_512" ->
  (fun x65 x67 x68 ->
    let CI.CPointer x66 = x65 in
    _11_EverCrypt_DRBG_instantiate_sha2_512 x66 x67 x68)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_instantiate_sha2_384" ->
  (fun x69 x71 x72 ->
    let CI.CPointer x70 = x69 in
    _10_EverCrypt_DRBG_instantiate_sha2_384 x70 x71 x72)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_instantiate_sha2_256" ->
  (fun x73 x75 x76 ->
    let CI.CPointer x74 = x73 in
    _9_EverCrypt_DRBG_instantiate_sha2_256 x74 x75 x76)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Bool)))),
  "EverCrypt_DRBG_instantiate_sha1" ->
  (fun x77 x79 x80 ->
    let CI.CPointer x78 = x77 in
    _8_EverCrypt_DRBG_instantiate_sha1 x78 x79 x80)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x82; _},
     Returns (CI.Pointer x84)),
  "EverCrypt_DRBG_create" ->
  (fun x81 ->
    let x83 = x82 x81 in CI.make_ptr x84 (_7_EverCrypt_DRBG_create x83))
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x86; _},
     Returns (CI.Primitive CI.Uint32_t)),
  "EverCrypt_DRBG_min_length" ->
  (fun x85 -> let x87 = x86 x85 in _6_EverCrypt_DRBG_min_length x87)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| (CI.Primitive CI.Uint32_t as x88),
  "EverCrypt_DRBG_max_additional_input_length" ->
  (CI.make_ptr x88 (_5_EverCrypt_DRBG_max_additional_input_length ()))
| (CI.Primitive CI.Uint32_t as x89),
  "EverCrypt_DRBG_max_personalization_string_length" ->
  (CI.make_ptr x89 (_4_EverCrypt_DRBG_max_personalization_string_length ()))
| (CI.Primitive CI.Uint32_t as x90), "EverCrypt_DRBG_max_length" ->
  (CI.make_ptr x90 (_3_EverCrypt_DRBG_max_length ()))
| (CI.Primitive CI.Uint32_t as x91), "EverCrypt_DRBG_max_output_length" ->
  (CI.make_ptr x91 (_2_EverCrypt_DRBG_max_output_length ()))
| (CI.Primitive CI.Uint32_t as x92), "EverCrypt_DRBG_reseed_interval" ->
  (CI.make_ptr x92 (_1_EverCrypt_DRBG_reseed_interval ()))
| _, s ->  Printf.ksprintf failwith "No match for %s" s
