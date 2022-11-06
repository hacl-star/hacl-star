module CI = Cstubs_internals

external _1_Hacl_NaCl_crypto_secretbox_detached
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  =
  "_1_Hacl_NaCl_crypto_secretbox_detached_byte6" "_1_Hacl_NaCl_crypto_secretbox_detached"
  

external _2_Hacl_NaCl_crypto_secretbox_open_detached
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  =
  "_2_Hacl_NaCl_crypto_secretbox_open_detached_byte6" "_2_Hacl_NaCl_crypto_secretbox_open_detached"
  

external _3_Hacl_NaCl_crypto_secretbox_easy
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32 = "_3_Hacl_NaCl_crypto_secretbox_easy" 

external _4_Hacl_NaCl_crypto_secretbox_open_easy
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32
  = "_4_Hacl_NaCl_crypto_secretbox_open_easy" 

external _5_Hacl_NaCl_crypto_box_beforenm
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  = "_5_Hacl_NaCl_crypto_box_beforenm" 

external _6_Hacl_NaCl_crypto_box_detached_afternm
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  =
  "_6_Hacl_NaCl_crypto_box_detached_afternm_byte6" "_6_Hacl_NaCl_crypto_box_detached_afternm"
  

external _7_Hacl_NaCl_crypto_box_detached
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  =
  "_7_Hacl_NaCl_crypto_box_detached_byte7" "_7_Hacl_NaCl_crypto_box_detached" 

external _8_Hacl_NaCl_crypto_box_open_detached_afternm
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  =
  "_8_Hacl_NaCl_crypto_box_open_detached_afternm_byte6" "_8_Hacl_NaCl_crypto_box_open_detached_afternm"
  

external _9_Hacl_NaCl_crypto_box_open_detached
  : bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 ->
    bytes CI.ocaml -> bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  =
  "_9_Hacl_NaCl_crypto_box_open_detached_byte7" "_9_Hacl_NaCl_crypto_box_open_detached"
  

external _10_Hacl_NaCl_crypto_box_easy_afternm
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32
  = "_10_Hacl_NaCl_crypto_box_easy_afternm" 

external _11_Hacl_NaCl_crypto_box_easy
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
  = "_11_Hacl_NaCl_crypto_box_easy_byte6" "_11_Hacl_NaCl_crypto_box_easy" 

external _12_Hacl_NaCl_crypto_box_open_easy_afternm
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> Unsigned.uint32
  = "_12_Hacl_NaCl_crypto_box_open_easy_afternm" 

external _13_Hacl_NaCl_crypto_box_open_easy
  : bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml ->
    bytes CI.ocaml -> bytes CI.ocaml -> Unsigned.uint32
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
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes,
                 Function
                   (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_box_open_easy" -> _13_Hacl_NaCl_crypto_box_open_easy
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_NaCl_crypto_box_open_easy_afternm" ->
  _12_Hacl_NaCl_crypto_box_open_easy_afternm
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes,
                 Function
                   (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_box_easy" -> _11_Hacl_NaCl_crypto_box_easy
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_NaCl_crypto_box_easy_afternm" ->
  _10_Hacl_NaCl_crypto_box_easy_afternm
| Function
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
                   (CI.OCaml CI.Bytes,
                    Function
                      (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))))))),
  "Hacl_NaCl_crypto_box_open_detached" ->
  _9_Hacl_NaCl_crypto_box_open_detached
| Function
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
                   (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_box_open_detached_afternm" ->
  _8_Hacl_NaCl_crypto_box_open_detached_afternm
| Function
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
                   (CI.OCaml CI.Bytes,
                    Function
                      (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))))))),
  "Hacl_NaCl_crypto_box_detached" -> _7_Hacl_NaCl_crypto_box_detached
| Function
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
                   (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_box_detached_afternm" ->
  _6_Hacl_NaCl_crypto_box_detached_afternm
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))),
  "Hacl_NaCl_crypto_box_beforenm" -> _5_Hacl_NaCl_crypto_box_beforenm
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_NaCl_crypto_secretbox_open_easy" ->
  _4_Hacl_NaCl_crypto_secretbox_open_easy
| Function
    (CI.OCaml CI.Bytes,
     Function
       (CI.OCaml CI.Bytes,
        Function
          (CI.Primitive CI.Uint32_t,
           Function
             (CI.OCaml CI.Bytes,
              Function
                (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t)))))),
  "Hacl_NaCl_crypto_secretbox_easy" -> _3_Hacl_NaCl_crypto_secretbox_easy
| Function
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
                   (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_secretbox_open_detached" ->
  _2_Hacl_NaCl_crypto_secretbox_open_detached
| Function
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
                   (CI.OCaml CI.Bytes, Returns (CI.Primitive CI.Uint32_t))))))),
  "Hacl_NaCl_crypto_secretbox_detached" ->
  _1_Hacl_NaCl_crypto_secretbox_detached
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
