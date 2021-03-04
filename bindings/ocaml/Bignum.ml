open Ctypes
open Unsigned

open SharedDefs
module C = CBytes

module Hacl_Bignum256 = Hacl_Bignum256_bindings.Bindings(Hacl_Bignum256_stubs)
module Hacl_Bignum4096 = Hacl_Bignum4096_bindings.Bindings(Hacl_Bignum4096_stubs)

module type Bignum = sig
  type t
  val size : int
  val from_bytes : Bytes.t -> t
  val to_bytes : t -> Bytes.t
end

module Make_Bignum
    (Impl : sig
       type t
       val size : int
       val from_bytes : uint32 -> CBytes.buf -> t
       val to_bytes : t -> CBytes.buf -> unit
  end)
= struct
  type t = uint64 ptr
  let size = Impl.size
  let from_bytes b =
     Impl.from_bytes (UInt32.of_int (Bytes.length b)) (C.ctypes_buf b)
  let to_bytes bn =
    let out = Bytes.make Impl.size '\x00' in
    Impl.to_bytes bn (C.ctypes_buf out);
    out
end

module Bignum256 : Bignum =
  Make_Bignum (struct
    type t = uint64 ptr
    let size = 32
    let from_bytes = Hacl_Bignum256.hacl_Bignum256_new_bn_from_bytes_be
    let to_bytes = Hacl_Bignum256.hacl_Bignum256_bn_to_bytes_be
  end)

module Bignum4096 : Bignum =
  Make_Bignum (struct
    type t = uint64 ptr
    let size = 512
    let from_bytes = Hacl_Bignum4096.hacl_Bignum4096_new_bn_from_bytes_be
    let to_bytes = Hacl_Bignum4096.hacl_Bignum4096_bn_to_bytes_be
  end)
