module CI = Cstubs_internals

external _1_Hacl_Streaming_Blake2_blocks_state_len
  : Unsigned.uint8 -> Unsigned.uint8 -> Unsigned.uint32
  = "_1_Hacl_Streaming_Blake2_blocks_state_len" 

external _2_Hacl_Streaming_Blake2_blake2s_32_no_key_create_in
  : unit -> CI.voidp = "_2_Hacl_Streaming_Blake2_blake2s_32_no_key_create_in" 

external _3_Hacl_Streaming_Blake2_blake2s_32_no_key_init
  : _ CI.fatptr -> unit = "_3_Hacl_Streaming_Blake2_blake2s_32_no_key_init" 

external _4_Hacl_Streaming_Blake2_blake2s_32_no_key_update
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> Unsigned.uint32
  = "_4_Hacl_Streaming_Blake2_blake2s_32_no_key_update" 

external _5_Hacl_Streaming_Blake2_blake2s_32_no_key_finish
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_5_Hacl_Streaming_Blake2_blake2s_32_no_key_finish" 

external _6_Hacl_Streaming_Blake2_blake2s_32_no_key_free
  : _ CI.fatptr -> unit = "_6_Hacl_Streaming_Blake2_blake2s_32_no_key_free" 

external _7_Hacl_Streaming_Blake2_blake2b_32_no_key_create_in
  : unit -> CI.voidp = "_7_Hacl_Streaming_Blake2_blake2b_32_no_key_create_in" 

external _8_Hacl_Streaming_Blake2_blake2b_32_no_key_init
  : _ CI.fatptr -> unit = "_8_Hacl_Streaming_Blake2_blake2b_32_no_key_init" 

external _9_Hacl_Streaming_Blake2_blake2b_32_no_key_update
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> Unsigned.uint32
  = "_9_Hacl_Streaming_Blake2_blake2b_32_no_key_update" 

external _10_Hacl_Streaming_Blake2_blake2b_32_no_key_finish
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_10_Hacl_Streaming_Blake2_blake2b_32_no_key_finish" 

external _11_Hacl_Streaming_Blake2_blake2b_32_no_key_free
  : _ CI.fatptr -> unit = "_11_Hacl_Streaming_Blake2_blake2b_32_no_key_free" 

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
| Function (CI.Pointer _, Returns CI.Void),
  "Hacl_Streaming_Blake2_blake2b_32_no_key_free" ->
  (fun x1 ->
    let CI.CPointer x2 = x1 in
    _11_Hacl_Streaming_Blake2_blake2b_32_no_key_free x2)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Streaming_Blake2_blake2b_32_no_key_finish" ->
  (fun x3 x5 ->
    let CI.CPointer x4 = x3 in
    _10_Hacl_Streaming_Blake2_blake2b_32_no_key_finish x4 x5)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_Streaming_Blake2_blake2b_32_no_key_update" ->
  (fun x6 x8 x9 ->
    let CI.CPointer x7 = x6 in
    _9_Hacl_Streaming_Blake2_blake2b_32_no_key_update x7 x8 x9)
| Function (CI.Pointer _, Returns CI.Void),
  "Hacl_Streaming_Blake2_blake2b_32_no_key_init" ->
  (fun x10 ->
    let CI.CPointer x11 = x10 in
    _8_Hacl_Streaming_Blake2_blake2b_32_no_key_init x11)
| Function (CI.Void, Returns (CI.Pointer x13)),
  "Hacl_Streaming_Blake2_blake2b_32_no_key_create_in" ->
  (fun x12 ->
    CI.make_ptr x13
      (_7_Hacl_Streaming_Blake2_blake2b_32_no_key_create_in x12))
| Function (CI.Pointer _, Returns CI.Void),
  "Hacl_Streaming_Blake2_blake2s_32_no_key_free" ->
  (fun x14 ->
    let CI.CPointer x15 = x14 in
    _6_Hacl_Streaming_Blake2_blake2s_32_no_key_free x15)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Streaming_Blake2_blake2s_32_no_key_finish" ->
  (fun x16 x18 ->
    let CI.CPointer x17 = x16 in
    _5_Hacl_Streaming_Blake2_blake2s_32_no_key_finish x17 x18)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_Streaming_Blake2_blake2s_32_no_key_update" ->
  (fun x19 x21 x22 ->
    let CI.CPointer x20 = x19 in
    _4_Hacl_Streaming_Blake2_blake2s_32_no_key_update x20 x21 x22)
| Function (CI.Pointer _, Returns CI.Void),
  "Hacl_Streaming_Blake2_blake2s_32_no_key_init" ->
  (fun x23 ->
    let CI.CPointer x24 = x23 in
    _3_Hacl_Streaming_Blake2_blake2s_32_no_key_init x24)
| Function (CI.Void, Returns (CI.Pointer x26)),
  "Hacl_Streaming_Blake2_blake2s_32_no_key_create_in" ->
  (fun x25 ->
    CI.make_ptr x26
      (_2_Hacl_Streaming_Blake2_blake2s_32_no_key_create_in x25))
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x28; _},
     Function
       (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x31; _},
        Returns (CI.Primitive CI.Uint32_t))),
  "Hacl_Streaming_Blake2_blocks_state_len" ->
  (fun x27 x30 ->
    let x29 = x28 x27 in
    let x32 = x31 x30 in _1_Hacl_Streaming_Blake2_blocks_state_len x29 x32)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
