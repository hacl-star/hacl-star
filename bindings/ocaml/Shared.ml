open Ctypes
open Unsigned
open Utils

module type Chacha20_Poly1305 = sig
  val encrypt: Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val decrypt: Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module Make_Chacha20_Poly1305 (Impl : sig
    val encrypt : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> uint8 ptr -> unit
    val decrypt : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> uint8 ptr -> uint32
  end)
= struct
  let encrypt key iv ad pt ct tag =
    Impl.encrypt (uint8_ptr key) (uint8_ptr iv) (size_uint32 ad) (uint8_ptr ad)
      (size_uint32 pt) (uint8_ptr pt) (uint8_ptr ct) (uint8_ptr tag)

  let decrypt key iv ad pt ct tag =
    let result = Impl.decrypt (uint8_ptr key) (uint8_ptr iv) (size_uint32 ad) (uint8_ptr ad)
        (size_uint32 pt) (uint8_ptr pt) (uint8_ptr ct) (uint8_ptr tag)
    in
    UInt32.to_int result = 0
end

module type Curve25519 = sig
  val secret_to_public : Bigstring.t -> Bigstring.t -> unit
  val scalarmult : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val ecdh : Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module Make_Curve25519 (Impl : sig
    val secret_to_public : uint8 ptr -> uint8 ptr -> unit
    val scalarmult : uint8 ptr -> uint8 ptr -> uint8 ptr -> unit
    val ecdh : uint8 ptr -> uint8 ptr -> uint8 ptr -> bool
  end)
= struct
  let secret_to_public pub priv = Impl.secret_to_public (uint8_ptr pub) (uint8_ptr priv)
  let scalarmult shared my_priv their_pub = Impl.scalarmult (uint8_ptr shared) (uint8_ptr my_priv) (uint8_ptr their_pub)
  let ecdh shared my_priv their_pub = Impl.ecdh (uint8_ptr shared) (uint8_ptr my_priv) (uint8_ptr their_pub)
end
