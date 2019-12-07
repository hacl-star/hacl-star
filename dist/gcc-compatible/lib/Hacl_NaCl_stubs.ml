module CI = Cstubs_internals

external _1_Hacl_NaCl_crypto_secretbox_detached
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  =
  "_1_Hacl_NaCl_crypto_secretbox_detached_byte6" "_1_Hacl_NaCl_crypto_secretbox_detached"
  

external _2_Hacl_NaCl_crypto_secretbox_open_detached
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  =
  "_2_Hacl_NaCl_crypto_secretbox_open_detached_byte6" "_2_Hacl_NaCl_crypto_secretbox_open_detached"
  

external _3_Hacl_NaCl_crypto_secretbox_easy
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> Unsigned.uint32 = "_3_Hacl_NaCl_crypto_secretbox_easy" 

external _4_Hacl_NaCl_crypto_secretbox_open_easy
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> Unsigned.uint32
  = "_4_Hacl_NaCl_crypto_secretbox_open_easy" 

external _5_Hacl_NaCl_crypto_box_beforenm
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  = "_5_Hacl_NaCl_crypto_box_beforenm" 

external _6_Hacl_NaCl_crypto_box_detached_afternm
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  =
  "_6_Hacl_NaCl_crypto_box_detached_afternm_byte6" "_6_Hacl_NaCl_crypto_box_detached_afternm"
  

external _7_Hacl_NaCl_crypto_box_detached
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  =
  "_7_Hacl_NaCl_crypto_box_detached_byte7" "_7_Hacl_NaCl_crypto_box_detached" 

external _8_Hacl_NaCl_crypto_box_open_detached_afternm
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  =
  "_8_Hacl_NaCl_crypto_box_open_detached_afternm_byte6" "_8_Hacl_NaCl_crypto_box_open_detached_afternm"
  

external _9_Hacl_NaCl_crypto_box_open_detached
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 ->
    _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  =
  "_9_Hacl_NaCl_crypto_box_open_detached_byte7" "_9_Hacl_NaCl_crypto_box_open_detached"
  

external _10_Hacl_NaCl_crypto_box_easy_afternm
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> Unsigned.uint32 = "_10_Hacl_NaCl_crypto_box_easy_afternm" 

external _11_Hacl_NaCl_crypto_box_easy
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  = "_11_Hacl_NaCl_crypto_box_easy_byte6" "_11_Hacl_NaCl_crypto_box_easy" 

external _12_Hacl_NaCl_crypto_box_open_easy_afternm
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> Unsigned.uint32
  = "_12_Hacl_NaCl_crypto_box_open_easy_afternm" 

external _13_Hacl_NaCl_crypto_box_open_easy
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32 -> _ CI.fatptr ->
    _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint32
  =
  "_13_Hacl_NaCl_crypto_box_open_easy_byte6" "_13_Hacl_NaCl_crypto_box_open_easy"
  

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
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _,
                 Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_box_open_easy" ->
  (fun x1 x2 x3 x4 x5 x6 ->
    _13_Hacl_NaCl_crypto_box_open_easy (CI.cptr x1) (CI.cptr x2) x3
    (CI.cptr x4) (CI.cptr x5) (CI.cptr x6))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_NaCl_crypto_box_open_easy_afternm" ->
  (fun x7 x8 x9 x10 x11 ->
    _12_Hacl_NaCl_crypto_box_open_easy_afternm (CI.cptr x7) (CI.cptr x8) x9
    (CI.cptr x10) (CI.cptr x11))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function
                (CI.Pointer _,
                 Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_box_easy" ->
  (fun x12 x13 x14 x15 x16 x17 ->
    _11_Hacl_NaCl_crypto_box_easy (CI.cptr x12) (CI.cptr x13) x14
    (CI.cptr x15) (CI.cptr x16) (CI.cptr x17))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_NaCl_crypto_box_easy_afternm" ->
  (fun x18 x19 x20 x21 x22 ->
    _10_Hacl_NaCl_crypto_box_easy_afternm (CI.cptr x18) (CI.cptr x19) x20
    (CI.cptr x21) (CI.cptr x22))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function
                   (CI.Pointer _,
                    Function
                      (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))))))),
  "Hacl_NaCl_crypto_box_open_detached" ->
  (fun x23 x24 x25 x26 x27 x28 x29 ->
    _9_Hacl_NaCl_crypto_box_open_detached (CI.cptr x23) (CI.cptr x24)
    (CI.cptr x25) x26 (CI.cptr x27) (CI.cptr x28) (CI.cptr x29))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_box_open_detached_afternm" ->
  (fun x30 x31 x32 x33 x34 x35 ->
    _8_Hacl_NaCl_crypto_box_open_detached_afternm (CI.cptr x30) (CI.cptr x31)
    (CI.cptr x32) x33 (CI.cptr x34) (CI.cptr x35))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function
                   (CI.Pointer _,
                    Function
                      (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))))))),
  "Hacl_NaCl_crypto_box_detached" ->
  (fun x36 x37 x38 x39 x40 x41 x42 ->
    _7_Hacl_NaCl_crypto_box_detached (CI.cptr x36) (CI.cptr x37)
    (CI.cptr x38) x39 (CI.cptr x40) (CI.cptr x41) (CI.cptr x42))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_box_detached_afternm" ->
  (fun x43 x44 x45 x46 x47 x48 ->
    _6_Hacl_NaCl_crypto_box_detached_afternm (CI.cptr x43) (CI.cptr x44)
    (CI.cptr x45) x46 (CI.cptr x47) (CI.cptr x48))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_NaCl_crypto_box_beforenm" ->
  (fun x49 x50 x51 ->
    _5_Hacl_NaCl_crypto_box_beforenm (CI.cptr x49) (CI.cptr x50)
    (CI.cptr x51))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_NaCl_crypto_secretbox_open_easy" ->
  (fun x52 x53 x54 x55 x56 ->
    _4_Hacl_NaCl_crypto_secretbox_open_easy (CI.cptr x52) (CI.cptr x53) x54
    (CI.cptr x55) (CI.cptr x56))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.Pointer _,
              Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_NaCl_crypto_secretbox_easy" ->
  (fun x57 x58 x59 x60 x61 ->
    _3_Hacl_NaCl_crypto_secretbox_easy (CI.cptr x57) (CI.cptr x58) x59
    (CI.cptr x60) (CI.cptr x61))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_secretbox_open_detached" ->
  (fun x62 x63 x64 x65 x66 x67 ->
    _2_Hacl_NaCl_crypto_secretbox_open_detached (CI.cptr x62) (CI.cptr x63)
    (CI.cptr x64) x65 (CI.cptr x66) (CI.cptr x67))
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _,
        Function
          (CI.Pointer _,
           Function
             (CI.Primitive CI.Uint32_t,
              Function
                (CI.Pointer _,
                 Function (CI.Pointer _, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_secretbox_detached" ->
  (fun x68 x69 x70 x71 x72 x73 ->
    _1_Hacl_NaCl_crypto_secretbox_detached (CI.cptr x68) (CI.cptr x69)
    (CI.cptr x70) x71 (CI.cptr x72) (CI.cptr x73))
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
