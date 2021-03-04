open Ctypes
open Unsigned

open SharedDefs
module C = CBytes

let unpad b =
  let l = ref 0 in
  while !l < Bytes.length b && Bytes.get b !l = '\x00' do
    l := !l + 1
  done;
  Bytes.sub b !l (Bytes.length b - !l)

module Hacl_Bignum256 = Hacl_Bignum256_bindings.Bindings(Hacl_Bignum256_stubs)
module Hacl_Bignum4096 = Hacl_Bignum4096_bindings.Bindings(Hacl_Bignum4096_stubs)

module type Bignum = sig
  type t
  val size : int
  val from_bytes_pad : buf:Bytes.t -> t
  val from_bytes : buf:Bytes.t -> t
  val to_bytes_unpad : bn:t -> Bytes.t
  val to_bytes : bn:t -> Bytes.t
  val mod_exp_raw : n:t -> a:t -> b:t -> t option
end

module Make_Bignum
    (Impl : sig
       type t
       val size : int
       val from_bytes : uint32 -> CBytes.buf -> t
       val to_bytes : t -> CBytes.buf -> unit
       val mod_exp_raw : t -> t -> uint32 -> t -> t -> bool
  end)
= struct
  type t = uint64 ptr
  let size = Impl.size
  let from_bytes_pad ~buf =
    (* TODO: this constraint is too rigid, revise *)
    assert (Bytes.length buf <= size);
    let buf = Bytes.cat (Bytes.make (size - (Bytes.length buf)) '\x00') buf in
    Impl.from_bytes (UInt32.of_int size) (C.ctypes_buf buf)
  let from_bytes ~buf =
    assert (Bytes.length buf <= size);
    Impl.from_bytes (UInt32.of_int (Bytes.length buf)) (C.ctypes_buf buf)
  let to_bytes ~bn =
    let out = Bytes.make size '\x00' in
    Impl.to_bytes bn (C.ctypes_buf out);
    out
  let to_bytes_unpad ~bn =
    let out = to_bytes ~bn in
    unpad out
  let mod_exp_raw ~n ~a ~b =
    let res = from_bytes ~buf:(Bytes.make size '\x00') in
    if Impl.mod_exp_raw n a (UInt32.of_int (8 * size)) b res then
      Some res
    else
      None
end

module Bignum256 : Bignum =
  Make_Bignum (struct
    type t = uint64 ptr
    let size = 32
    let from_bytes = Hacl_Bignum256.hacl_Bignum256_new_bn_from_bytes_be
    let to_bytes = Hacl_Bignum256.hacl_Bignum256_bn_to_bytes_be
    let mod_exp_raw = Hacl_Bignum256.hacl_Bignum256_mod_exp_raw
  end)

module Bignum4096 : Bignum =
  Make_Bignum (struct
    type t = uint64 ptr
    let size = 512
    let from_bytes = Hacl_Bignum4096.hacl_Bignum4096_new_bn_from_bytes_be
    let to_bytes = Hacl_Bignum4096.hacl_Bignum4096_bn_to_bytes_be
    let mod_exp_raw = Hacl_Bignum4096.hacl_Bignum4096_mod_exp_raw
  end)
