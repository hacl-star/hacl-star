open Ctypes
open PosixTypes
open Foreign
open Ctypes_static
open Unsigned

open Utils

module Hacl_Chacha20Poly1305_32 = Hacl_Chacha20Poly1305_32_bindings.Bindings(Hacl_Chacha20Poly1305_32_stubs)
module Hacl_Chacha20Poly1305_128 = Hacl_Chacha20Poly1305_128_bindings.Bindings(Hacl_Chacha20Poly1305_128_stubs)
module Hacl_Chacha20Poly1305_256 = Hacl_Chacha20Poly1305_256_bindings.Bindings(Hacl_Chacha20Poly1305_256_stubs)

module type Chacha20_Poly1305 = sig
  val encrypt: Bigstring.t -> Bigstring.t -> int -> Bigstring.t -> int -> Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val decrypt: Bigstring.t -> Bigstring.t -> int -> Bigstring.t -> int -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module Make_Chacha20_Poly1305 (Impl : sig
    val encrypt : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> uint8 ptr -> unit
    val decrypt : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> uint8 ptr -> uint32
end)
  = struct
    let encrypt key iv ad_len ad pt_len pt ct tag =
      let key = uint8_ptr_of_bigstring key in
      let iv = uint8_ptr_of_bigstring iv in
      let ad = uint8_ptr_of_bigstring ad in
      let pt = uint8_ptr_of_bigstring pt in
      let ct = uint8_ptr_of_bigstring ct in
      let tag = uint8_ptr_of_bigstring tag in
      Impl.encrypt key iv (UInt32.of_int ad_len) ad (UInt32.of_int pt_len) pt ct tag

    let decrypt key iv ad_len ad pt_len pt ct tag =
      let key = uint8_ptr_of_bigstring key in
      let iv = uint8_ptr_of_bigstring iv in
      let ad = uint8_ptr_of_bigstring ad in
      let pt = uint8_ptr_of_bigstring pt in
      let ct = uint8_ptr_of_bigstring ct in
      let tag = uint8_ptr_of_bigstring tag in
      let result = Impl.decrypt key iv (UInt32.of_int ad_len) ad (UInt32.of_int pt_len) pt ct tag in
      UInt32.to_int result = 0
end

module Chacha20_Poly1305_32 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let encrypt = Hacl_Chacha20Poly1305_32.hacl_Chacha20Poly1305_32_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_32.hacl_Chacha20Poly1305_32_aead_decrypt
  end)

module Chacha20_Poly1305_128 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let encrypt = Hacl_Chacha20Poly1305_128.hacl_Chacha20Poly1305_128_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_128.hacl_Chacha20Poly1305_128_aead_decrypt
  end)

module Chacha20_Poly1305_256 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let encrypt = Hacl_Chacha20Poly1305_256.hacl_Chacha20Poly1305_256_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_256.hacl_Chacha20Poly1305_256_aead_decrypt
  end)
