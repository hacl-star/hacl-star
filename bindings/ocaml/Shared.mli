open Ctypes
open Unsigned

module type Chacha20_Poly1305 = sig
  val encrypt: Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val decrypt: Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module Make_Chacha20_Poly1305 (Impl : sig
    val encrypt : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> uint8 ptr -> unit
    val decrypt : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> uint8 ptr -> uint32
  end) : Chacha20_Poly1305

module type Curve25519 = sig
  val secret_to_public : Bigstring.t -> Bigstring.t -> unit
  val scalarmult : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val ecdh : Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module Make_Curve25519 (Impl : sig
    val secret_to_public : uint8 ptr -> uint8 ptr -> unit
    val scalarmult : uint8 ptr -> uint8 ptr -> uint8 ptr -> unit
    val ecdh : uint8 ptr -> uint8 ptr -> uint8 ptr -> bool
  end) : Curve25519

module type EdDSA = sig
  val secret_to_public : Bigstring.t -> Bigstring.t -> unit
  val sign : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val verify : Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
  val expand_keys : Bigstring.t -> Bigstring.t -> unit
  val sign_expanded : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module Make_EdDSA (Impl : sig
  val secret_to_public : uint8 ptr -> uint8 ptr -> unit
  val sign : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> unit
  val verify : uint8 ptr ->uint32 -> uint8 ptr -> uint8 ptr -> bool
  val expand_keys : uint8 ptr -> uint8 ptr -> unit
  val sign_expanded : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> unit
  end) : EdDSA

module type HashFunction = sig
  val hash : Bigstring.t -> Bigstring.t -> unit
end

module Make_HashFunction (Impl : sig
    val hash : uint8 ptr -> uint32 -> uint8 ptr -> unit
  end) : HashFunction

module type MAC = sig
  val mac : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module Make_Poly1305 (Impl : sig
    val mac : uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> unit
  end) : MAC

module Make_HMAC (Impl : sig
    val mac : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> unit
  end) : MAC


module type HKDF = sig
  val expand: Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val extract: Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module Make_HKDF (Impl: sig
    val expand : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint32 -> unit
    val extract : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> unit
end) : HKDF
