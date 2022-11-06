module CI = Cstubs_internals

external _1_Hacl_Impl_SHA3_rotl
  : Unsigned.uint64 -> Unsigned.uint32 -> Unsigned.uint64
  = "_1_Hacl_Impl_SHA3_rotl" 

external _2_Hacl_Impl_SHA3_state_permute : _ CI.fatptr -> unit
  = "_2_Hacl_Impl_SHA3_state_permute" 

external _3_Hacl_Impl_SHA3_loadState
  : Unsigned.uint32 -> bytes CI.ocaml -> _ CI.fatptr -> unit
  = "_3_Hacl_Impl_SHA3_loadState" 

external _4_Hacl_Impl_SHA3_storeState
  : Unsigned.uint32 -> _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_4_Hacl_Impl_SHA3_storeState" 

external _5_Hacl_Impl_SHA3_absorb
  : _ CI.fatptr -> Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint8 -> unit = "_5_Hacl_Impl_SHA3_absorb" 

external _6_Hacl_Impl_SHA3_squeeze
  : _ CI.fatptr -> Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml ->
    unit = "_6_Hacl_Impl_SHA3_squeeze" 

external _7_Hacl_Impl_SHA3_keccak
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 ->
    bytes CI.ocaml -> Unsigned.uint8 -> Unsigned.uint32 -> bytes CI.ocaml ->
    unit = "_7_Hacl_Impl_SHA3_keccak_byte7" "_7_Hacl_Impl_SHA3_keccak" 

external _8_Hacl_SHA3_shake128_hacl
  : Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    unit = "_8_Hacl_SHA3_shake128_hacl" 

external _9_Hacl_SHA3_shake256_hacl
  : Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    unit = "_9_Hacl_SHA3_shake256_hacl" 

external _10_Hacl_SHA3_sha3_224
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_10_Hacl_SHA3_sha3_224" 

external _11_Hacl_SHA3_sha3_256
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_11_Hacl_SHA3_sha3_256" 

external _12_Hacl_SHA3_sha3_384
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_12_Hacl_SHA3_sha3_384" 

external _13_Hacl_SHA3_sha3_512
  : Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> unit
  = "_13_Hacl_SHA3_sha3_512" 

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
       (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_SHA3_sha3_512" -> _13_Hacl_SHA3_sha3_512
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_SHA3_sha3_384" -> _12_Hacl_SHA3_sha3_384
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_SHA3_sha3_256" -> _11_Hacl_SHA3_sha3_256
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_SHA3_sha3_224" -> _10_Hacl_SHA3_sha3_224
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_SHA3_shake256_hacl" -> _9_Hacl_SHA3_shake256_hacl
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_SHA3_shake128_hacl" -> _8_Hacl_SHA3_shake128_hacl
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint8_t,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function (CI.OCaml CI.Bytes, Returns CI.Void))))))),
  "Hacl_Impl_SHA3_keccak" -> _7_Hacl_Impl_SHA3_keccak
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function (CI.OCaml CI.Bytes, Returns CI.Void)))),
  "Hacl_Impl_SHA3_squeeze" ->
  (fun x28 x30 x31 x32 ->
    let CI.CPointer x29 = x28 in _6_Hacl_Impl_SHA3_squeeze x29 x30 x31 x32)
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function (CI.Primitive CI.Uint8_t, Returns CI.Void))))),
  "Hacl_Impl_SHA3_absorb" ->
  (fun x33 x35 x36 x37 x38 ->
    let CI.CPointer x34 = x33 in _5_Hacl_Impl_SHA3_absorb x34 x35 x36 x37 x38)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Impl_SHA3_storeState" ->
  (fun x39 x40 x42 ->
    let CI.CPointer x41 = x40 in _4_Hacl_Impl_SHA3_storeState x39 x41 x42)
| Function
    (CI.Primitive CI.Uint32_t,
     Function (CI.OCaml CI.Bytes, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_SHA3_loadState" ->
  (fun x43 x44 x45 ->
    let CI.CPointer x46 = x45 in _3_Hacl_Impl_SHA3_loadState x43 x44 x46)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Impl_SHA3_state_permute" ->
  (fun x47 ->
    let CI.CPointer x48 = x47 in _2_Hacl_Impl_SHA3_state_permute x48)
| Function
    (CI.Primitive CI.Uint64_t,
     Function (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Uint64_t))),
  "Hacl_Impl_SHA3_rotl" -> _1_Hacl_Impl_SHA3_rotl
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
