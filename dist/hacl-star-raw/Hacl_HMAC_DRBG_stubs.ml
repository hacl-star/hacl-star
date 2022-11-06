module CI = Cstubs_internals

external _1_Hacl_HMAC_DRBG_reseed_interval : unit -> CI.voidp
  = "_1_Hacl_HMAC_DRBG_reseed_interval" 

external _2_Hacl_HMAC_DRBG_max_output_length : unit -> CI.voidp
  = "_2_Hacl_HMAC_DRBG_max_output_length" 

external _3_Hacl_HMAC_DRBG_max_length : unit -> CI.voidp
  = "_3_Hacl_HMAC_DRBG_max_length" 

external _4_Hacl_HMAC_DRBG_max_personalization_string_length
  : unit -> CI.voidp = "_4_Hacl_HMAC_DRBG_max_personalization_string_length" 

external _5_Hacl_HMAC_DRBG_max_additional_input_length : unit -> CI.voidp
  = "_5_Hacl_HMAC_DRBG_max_additional_input_length" 

external _6_Hacl_HMAC_DRBG_min_length : Unsigned.uint8 -> Unsigned.uint32
  = "_6_Hacl_HMAC_DRBG_min_length" 

external _7_Hacl_HMAC_DRBG_create_in : Unsigned.uint8 -> CI.managed_buffer
  = "_7_Hacl_HMAC_DRBG_create_in" 

external _8_Hacl_HMAC_DRBG_instantiate
  : Unsigned.uint8 -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    unit
  = "_8_Hacl_HMAC_DRBG_instantiate_byte8" "_8_Hacl_HMAC_DRBG_instantiate" 

external _9_Hacl_HMAC_DRBG_reseed
  : Unsigned.uint8 -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_9_Hacl_HMAC_DRBG_reseed_byte6" "_9_Hacl_HMAC_DRBG_reseed" 

external _10_Hacl_HMAC_DRBG_generate
  : Unsigned.uint8 -> bytes CI.ocaml -> _ CI.fatptr -> Unsigned.uint32 ->
    Unsigned.uint32 -> bytes CI.ocaml -> bool
  = "_10_Hacl_HMAC_DRBG_generate_byte6" "_10_Hacl_HMAC_DRBG_generate" 

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
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x2; _},
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Struct _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Bool))))))),
  "Hacl_HMAC_DRBG_generate" ->
  (fun x1 x4 x5 x7 x8 x9 ->
    let CI.CPointer x6 = Ctypes.addr x5 in
    let x3 = x2 x1 in _10_Hacl_HMAC_DRBG_generate x3 x4 x6 x7 x8 x9)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x11; _},
     Function
       (CI.Struct _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function (CI.OCaml CI.Bytes, Returns CI.Void)))))),
  "Hacl_HMAC_DRBG_reseed" ->
  (fun x10 x13 x15 x16 x17 x18 ->
    let CI.CPointer x14 = Ctypes.addr x13 in
    let x12 = x11 x10 in _9_Hacl_HMAC_DRBG_reseed x12 x14 x15 x16 x17 x18)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x20; _},
     Function
       (CI.Struct _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.OCaml CI.Bytes,
                    Function
                      (CI.Primitive CI.Uint32_t,
                       Function (CI.OCaml CI.Bytes, Returns CI.Void)))))))),
  "Hacl_HMAC_DRBG_instantiate" ->
  (fun x19 x22 x24 x25 x26 x27 x28 x29 ->
    let CI.CPointer x23 = Ctypes.addr x22 in
    let x21 = x20 x19 in
    _8_Hacl_HMAC_DRBG_instantiate x21 x23 x24 x25 x26 x27 x28 x29)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x31; _},
     Returns (CI.Struct _ as x33)),
  "Hacl_HMAC_DRBG_create_in" ->
  (fun x30 ->
    let x32 = x31 x30 in
    CI.make_structured x33 (_7_Hacl_HMAC_DRBG_create_in x32))
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x35; _},
     Returns (CI.Primitive CI.Uint32_t)),
  "Hacl_HMAC_DRBG_min_length" ->
  (fun x34 -> let x36 = x35 x34 in _6_Hacl_HMAC_DRBG_min_length x36)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| (CI.Primitive CI.Uint32_t as x37),
  "Hacl_HMAC_DRBG_max_additional_input_length" ->
  (CI.make_ptr x37 (_5_Hacl_HMAC_DRBG_max_additional_input_length ()))
| (CI.Primitive CI.Uint32_t as x38),
  "Hacl_HMAC_DRBG_max_personalization_string_length" ->
  (CI.make_ptr x38 (_4_Hacl_HMAC_DRBG_max_personalization_string_length ()))
| (CI.Primitive CI.Uint32_t as x39), "Hacl_HMAC_DRBG_max_length" ->
  (CI.make_ptr x39 (_3_Hacl_HMAC_DRBG_max_length ()))
| (CI.Primitive CI.Uint32_t as x40), "Hacl_HMAC_DRBG_max_output_length" ->
  (CI.make_ptr x40 (_2_Hacl_HMAC_DRBG_max_output_length ()))
| (CI.Primitive CI.Uint32_t as x41), "Hacl_HMAC_DRBG_reseed_interval" ->
  (CI.make_ptr x41 (_1_Hacl_HMAC_DRBG_reseed_interval ()))
| _, s ->  Printf.ksprintf failwith "No match for %s" s
