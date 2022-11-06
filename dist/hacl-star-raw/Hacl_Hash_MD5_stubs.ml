module CI = Cstubs_internals

external _1_Hacl_Hash_Core_MD5_legacy_init : _ CI.fatptr -> unit
  = "_1_Hacl_Hash_Core_MD5_legacy_init" 

external _2_Hacl_Hash_Core_MD5_legacy_update
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_2_Hacl_Hash_Core_MD5_legacy_update" 

external _3_Hacl_Hash_Core_MD5_legacy_finish
  : _ CI.fatptr -> bytes CI.ocaml -> unit
  = "_3_Hacl_Hash_Core_MD5_legacy_finish" 

external _4_Hacl_Hash_MD5_legacy_update_multi
  : _ CI.fatptr -> bytes CI.ocaml -> Unsigned.uint32 -> unit
  = "_4_Hacl_Hash_MD5_legacy_update_multi" 

external _5_Hacl_Hash_MD5_legacy_update_last
  : _ CI.fatptr -> Unsigned.uint64 -> bytes CI.ocaml -> Unsigned.uint32 ->
    unit = "_5_Hacl_Hash_MD5_legacy_update_last" 

external _6_Hacl_Hash_MD5_legacy_hash
  : bytes CI.ocaml -> Unsigned.uint32 -> bytes CI.ocaml -> unit
  = "_6_Hacl_Hash_MD5_legacy_hash" 

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
       (CI.Primitive CI.Uint32_t,
        Function (CI.OCaml CI.Bytes, Returns CI.Void))),
  "Hacl_Hash_MD5_legacy_hash" -> _6_Hacl_Hash_MD5_legacy_hash
| Function
    (CI.Pointer _,
     Function
       (CI.Primitive CI.Uint64_t,
        Function
          (CI.OCaml CI.Bytes,
           Function (CI.Primitive CI.Uint32_t, Returns CI.Void)))),
  "Hacl_Hash_MD5_legacy_update_last" ->
  (fun x4 x6 x7 x8 ->
    let CI.CPointer x5 = x4 in
    _5_Hacl_Hash_MD5_legacy_update_last x5 x6 x7 x8)
| Function
    (CI.Pointer _,
     Function
       (CI.OCaml CI.Bytes,
        Function (CI.Primitive CI.Uint32_t, Returns CI.Void))),
  "Hacl_Hash_MD5_legacy_update_multi" ->
  (fun x9 x11 x12 ->
    let CI.CPointer x10 = x9 in
    _4_Hacl_Hash_MD5_legacy_update_multi x10 x11 x12)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_MD5_legacy_finish" ->
  (fun x13 x15 ->
    let CI.CPointer x14 = x13 in _3_Hacl_Hash_Core_MD5_legacy_finish x14 x15)
| Function (CI.Pointer _, Function (CI.OCaml CI.Bytes, Returns CI.Void)),
  "Hacl_Hash_Core_MD5_legacy_update" ->
  (fun x16 x18 ->
    let CI.CPointer x17 = x16 in _2_Hacl_Hash_Core_MD5_legacy_update x17 x18)
| Function (CI.Pointer _, Returns CI.Void), "Hacl_Hash_Core_MD5_legacy_init" ->
  (fun x19 ->
    let CI.CPointer x20 = x19 in _1_Hacl_Hash_Core_MD5_legacy_init x20)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
