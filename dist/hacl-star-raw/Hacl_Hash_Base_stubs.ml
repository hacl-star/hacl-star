module CI = Cstubs_internals

external _1_Hacl_Hash_Definitions_word_len
  : Unsigned.uint8 -> Unsigned.uint32 = "_1_Hacl_Hash_Definitions_word_len" 

external _2_Hacl_Hash_Definitions_block_len
  : Unsigned.uint8 -> Unsigned.uint32 = "_2_Hacl_Hash_Definitions_block_len" 

external _3_Hacl_Hash_Definitions_hash_word_len
  : Unsigned.uint8 -> Unsigned.uint32
  = "_3_Hacl_Hash_Definitions_hash_word_len" 

external _4_Hacl_Hash_Definitions_hash_len
  : Unsigned.uint8 -> Unsigned.uint32 = "_4_Hacl_Hash_Definitions_hash_len" 

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
     Returns (CI.Primitive CI.Uint32_t)),
  "Hacl_Hash_Definitions_hash_len" ->
  (fun x1 -> let x3 = x2 x1 in _4_Hacl_Hash_Definitions_hash_len x3)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x5; _},
     Returns (CI.Primitive CI.Uint32_t)),
  "Hacl_Hash_Definitions_hash_word_len" ->
  (fun x4 -> let x6 = x5 x4 in _3_Hacl_Hash_Definitions_hash_word_len x6)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x8; _},
     Returns (CI.Primitive CI.Uint32_t)),
  "Hacl_Hash_Definitions_block_len" ->
  (fun x7 -> let x9 = x8 x7 in _2_Hacl_Hash_Definitions_block_len x9)
| Function
    (CI.View {CI.ty = CI.Primitive CI.Uint8_t; write = x11; _},
     Returns (CI.Primitive CI.Uint32_t)),
  "Hacl_Hash_Definitions_word_len" ->
  (fun x10 -> let x12 = x11 x10 in _1_Hacl_Hash_Definitions_word_len x12)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
