module CI = Cstubs_internals

external _1_Hacl_RSAPSS_rsapss_sign
  : Unsigned.uint8 -> Unsigned.uint32 -> Unsigned.uint32 ->
    Unsigned.uint32 -> _ CI.fatptr -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bool
  = "_1_Hacl_RSAPSS_rsapss_sign_byte10" "_1_Hacl_RSAPSS_rsapss_sign" 

external _2_Hacl_RSAPSS_rsapss_verify
  : Unsigned.uint8 -> Unsigned.uint32 -> Unsigned.uint32 -> _ CI.fatptr ->
    Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> bool
  = "_2_Hacl_RSAPSS_rsapss_verify_byte9" "_2_Hacl_RSAPSS_rsapss_verify" 

external _3_Hacl_RSAPSS_new_rsapss_load_pkey
  : Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml ->
    CI.voidp = "_3_Hacl_RSAPSS_new_rsapss_load_pkey" 

external _4_Hacl_RSAPSS_new_rsapss_load_skey
  : Unsigned.uint32 -> Unsigned.uint32 -> Unsigned.uint32 ->
    bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> CI.voidp
  =
  "_4_Hacl_RSAPSS_new_rsapss_load_skey_byte6" "_4_Hacl_RSAPSS_new_rsapss_load_skey"
  

external _5_Hacl_RSAPSS_rsapss_skey_sign
  : Unsigned.uint8 -> Unsigned.uint32 -> Unsigned.uint32 ->
    Unsigned.uint32 -> bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> bool
  =
  "_5_Hacl_RSAPSS_rsapss_skey_sign_byte12" "_5_Hacl_RSAPSS_rsapss_skey_sign" 

external _6_Hacl_RSAPSS_rsapss_pkey_verify
  : Unsigned.uint8 -> Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32 -> Unsigned.uint32 -> bytes CI.ocaml ->
    Unsigned.uint32 -> bytes CI.ocaml -> bool
  =
  "_6_Hacl_RSAPSS_rsapss_pkey_verify_byte10" "_6_Hacl_RSAPSS_rsapss_pkey_verify"
  

external _7_Hacl_RSAPSS_mgf_hash
  : Unsigned.uint8 -> Unsigned.uint32 -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> unit = "_7_Hacl_RSAPSS_mgf_hash" 

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
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function
             (CI.Primitive CI.Uint32_t,
              Function (CI.OCaml CI.Bytes, Returns CI.Void))))),
  "Hacl_RSAPSS_mgf_hash" ->
  (fun x1 x4 x5 x6 x7 ->
    let x3 = x2 x1 in _7_Hacl_RSAPSS_mgf_hash x3 x4 x5 x6 x7)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x9; _},
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function
                      (CI.Primitive CI.Uint32_t,
                       Function
                         (CI.OCaml CI.Bytes,
                          Function
                            (CI.Primitive CI.Uint32_t,
                             Function
                               (CI.OCaml CI.Bytes,
                                Returns (CI.Primitive CI.Bool))))))))))),
  "Hacl_RSAPSS_rsapss_pkey_verify" ->
  (fun x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 ->
    let x10 = x9 x8 in
    _6_Hacl_RSAPSS_rsapss_pkey_verify x10 x11 x12 x13 x14 x15 x16 x17 x18 x19)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x21; _},
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Primitive CI.Uint32_t,
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
                               (CI.Primitive CI.Uint32_t,
                                Function
                                  (CI.OCaml CI.Bytes,
                                   Function
                                     (CI.OCaml CI.Bytes,
                                      Returns (CI.Primitive CI.Bool))))))))))))),
  "Hacl_RSAPSS_rsapss_skey_sign" ->
  (fun x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 ->
    let x22 = x21 x20 in
    _5_Hacl_RSAPSS_rsapss_skey_sign x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    x32 x33)
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes,
                 Function (CI.OCaml CI.Bytes, Returns (CI.Pointer x40))))))),
  "Hacl_RSAPSS_new_rsapss_load_skey" ->
  (fun x34 x35 x36 x37 x38 x39 ->
    CI.make_ptr x40
      (_4_Hacl_RSAPSS_new_rsapss_load_skey x34 x35 x36 x37 x38 x39))
| Function
    (CI.Primitive CI.Uint32_t,
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.OCaml CI.Bytes, Returns (CI.Pointer x45))))),
  "Hacl_RSAPSS_new_rsapss_load_pkey" ->
  (fun x41 x42 x43 x44 ->
    CI.make_ptr x45 (_3_Hacl_RSAPSS_new_rsapss_load_pkey x41 x42 x43 x44))
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x47; _},
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Primitive CI.Uint32_t,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function
                      (CI.OCaml CI.Bytes,
                       Function
                         (CI.Primitive CI.Uint32_t,
                          Function
                            (CI.OCaml CI.Bytes,
                             Returns (CI.Primitive CI.Bool)))))))))),
  "Hacl_RSAPSS_rsapss_verify" ->
  (fun x46 x49 x50 x51 x53 x54 x55 x56 x57 ->
    let CI.CPointer x52 = x51 in
    let x48 = x47 x46 in
    _2_Hacl_RSAPSS_rsapss_verify x48 x49 x50 x52 x53 x54 x55 x56 x57)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x59; _},
     Function
       (CI.Primitive CI.Uint32_t,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function
                   (CI.Primitive CI.Uint32_t,
                    Function
                      (CI.OCaml CI.Bytes,
                       Function
                         (CI.Primitive CI.Uint32_t,
                          Function
                            (CI.OCaml CI.Bytes,
                             Function
                               (CI.OCaml CI.Bytes,
                                Returns (CI.Primitive CI.Bool))))))))))),
  "Hacl_RSAPSS_rsapss_sign" ->
  (fun x58 x61 x62 x63 x64 x66 x67 x68 x69 x70 ->
    let CI.CPointer x65 = x64 in
    let x60 = x59 x58 in
    _1_Hacl_RSAPSS_rsapss_sign x60 x61 x62 x63 x65 x66 x67 x68 x69 x70)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
