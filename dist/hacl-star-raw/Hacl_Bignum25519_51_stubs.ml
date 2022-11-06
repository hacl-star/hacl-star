module CI = Cstubs_internals

external _1_Hacl_Impl_Curve25519_Field51_fadd
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_1_Hacl_Impl_Curve25519_Field51_fadd" 

external _2_Hacl_Impl_Curve25519_Field51_fsub
  : _ CI.fatptr -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_2_Hacl_Impl_Curve25519_Field51_fsub" 

external _3_Hacl_Impl_Curve25519_Field51_fmul1
  : _ CI.fatptr -> _ CI.fatptr -> Unsigned.uint64 -> unit
  = "_3_Hacl_Impl_Curve25519_Field51_fmul1" 

external _4_Hacl_Impl_Curve25519_Field51_store_felem
  : _ CI.fatptr -> _ CI.fatptr -> unit
  = "_4_Hacl_Impl_Curve25519_Field51_store_felem" 

external _5_Hacl_Impl_Curve25519_Field51_cswap2
  : Unsigned.uint64 -> _ CI.fatptr -> _ CI.fatptr -> unit
  = "_5_Hacl_Impl_Curve25519_Field51_cswap2" 

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
    (CI.Primitive CI.Uint64_t,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_Curve25519_Field51_cswap2" ->
  (fun x1 x2 x4 ->
    let CI.CPointer x5 = x4 in
    let CI.CPointer x3 = x2 in
    _5_Hacl_Impl_Curve25519_Field51_cswap2 x1 x3 x5)
| Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void)),
  "Hacl_Impl_Curve25519_Field51_store_felem" ->
  (fun x6 x8 ->
    let CI.CPointer x9 = x8 in
    let CI.CPointer x7 = x6 in
    _4_Hacl_Impl_Curve25519_Field51_store_felem x7 x9)
| Function
    (CI.Pointer _,
     Function
       (CI.Pointer _, Function (CI.Primitive CI.Uint64_t, Returns CI.Void))),
  "Hacl_Impl_Curve25519_Field51_fmul1" ->
  (fun x10 x12 x14 ->
    let CI.CPointer x13 = x12 in
    let CI.CPointer x11 = x10 in
    _3_Hacl_Impl_Curve25519_Field51_fmul1 x11 x13 x14)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_Curve25519_Field51_fsub" ->
  (fun x15 x17 x19 ->
    let CI.CPointer x20 = x19 in
    let CI.CPointer x18 = x17 in
    let CI.CPointer x16 = x15 in
    _2_Hacl_Impl_Curve25519_Field51_fsub x16 x18 x20)
| Function
    (CI.Pointer _,
     Function (CI.Pointer _, Function (CI.Pointer _, Returns CI.Void))),
  "Hacl_Impl_Curve25519_Field51_fadd" ->
  (fun x21 x23 x25 ->
    let CI.CPointer x26 = x25 in
    let CI.CPointer x24 = x23 in
    let CI.CPointer x22 = x21 in
    _1_Hacl_Impl_Curve25519_Field51_fadd x22 x24 x26)
| _, s ->  Printf.ksprintf failwith "No match for %s" s


let foreign_value : type a. string -> a Ctypes.typ -> a Ctypes.ptr =
  fun name t -> match t, name with
| _, s ->  Printf.ksprintf failwith "No match for %s" s
