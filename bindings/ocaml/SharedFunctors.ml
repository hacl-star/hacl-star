open Ctypes
open Unsigned

open Utils
open SharedDefs

module Make_Chacha20_Poly1305 (Impl : sig
    val encrypt : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> uint8 ptr -> unit
    val decrypt : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> uint8 ptr -> uint32
  end) : Chacha20_Poly1305
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

module Make_Curve25519 (Impl : sig
    val secret_to_public : uint8 ptr -> uint8 ptr -> unit
    val scalarmult : uint8 ptr -> uint8 ptr -> uint8 ptr -> unit
    val ecdh : uint8 ptr -> uint8 ptr -> uint8 ptr -> bool
  end) : Curve25519
= struct
  let secret_to_public pub priv = Impl.secret_to_public (uint8_ptr pub) (uint8_ptr priv)
  let scalarmult shared my_priv their_pub = Impl.scalarmult (uint8_ptr shared) (uint8_ptr my_priv) (uint8_ptr their_pub)
  let ecdh shared my_priv their_pub = Impl.ecdh (uint8_ptr shared) (uint8_ptr my_priv) (uint8_ptr their_pub)
end

module Make_EdDSA (Impl : sig
  val secret_to_public : uint8 ptr -> uint8 ptr -> unit
  val sign : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> unit
  val verify : uint8 ptr ->uint32 -> uint8 ptr -> uint8 ptr -> bool
  val expand_keys : uint8 ptr -> uint8 ptr -> unit
  val sign_expanded : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> unit
  end) : EdDSA
= struct
  let secret_to_public pub priv = Impl.secret_to_public (uint8_ptr pub) (uint8_ptr priv)
  let sign signature priv msg = Impl.sign (uint8_ptr signature) (uint8_ptr priv) (size_uint32 msg) (uint8_ptr msg)
  let verify pub msg signature = Impl.verify (uint8_ptr pub) (size_uint32 msg) (uint8_ptr msg) (uint8_ptr signature)
  let expand_keys ks priv = Impl.expand_keys (uint8_ptr ks) (uint8_ptr priv)
  let sign_expanded signature ks msg = Impl.sign_expanded (uint8_ptr signature) (uint8_ptr ks) (size_uint32 msg) (uint8_ptr msg)
end

module Make_HashFunction (Impl : sig
    val hash_alg : HashDefs.alg option
    val hash : uint8 ptr -> uint32 -> uint8 ptr -> unit
  end) : HashFunction
= struct
  let hash input output =
    (match Impl.hash_alg with
    | Some alg -> assert (Bigstring.size output = HashDefs.digest_len alg)
    | None -> ());
    Impl.hash (uint8_ptr input) (size_uint32 input) (uint8_ptr output)
end

module Make_Poly1305 (Impl : sig
    val mac : uint8 ptr -> uint32 -> uint8 ptr -> uint8 ptr -> unit
  end) : MAC
= struct
  let mac dst key data = Impl.mac (uint8_ptr dst) (size_uint32 data) (uint8_ptr data) (uint8_ptr key)
end

module Make_HMAC (Impl : sig
    val mac : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> unit
  end) : MAC
= struct
  let mac dst key data = Impl.mac (uint8_ptr dst) (uint8_ptr key) (size_uint32 key) (uint8_ptr data) (size_uint32 data)
end

module Make_HKDF (Impl: sig
    val expand : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint32 -> unit
    val extract : uint8 ptr -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> unit
  end) : HKDF
  = struct
    let expand okm prk info = Impl.expand (uint8_ptr okm) (uint8_ptr prk) (size_uint32 prk) (uint8_ptr info) (size_uint32 info) (size_uint32 okm)
    let extract prk salt ikm = Impl.extract (uint8_ptr prk) (uint8_ptr salt) (size_uint32 salt) (uint8_ptr ikm) (size_uint32 ikm)
end

module Make_Blake2b (Impl : sig
    val blake2b : uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> uint32 -> uint8 ptr -> unit
  end) : Blake2b
= struct
  let hash key pt output = Impl.blake2b (size_uint32 output) (uint8_ptr output) (size_uint32 pt) (uint8_ptr pt) (size_uint32 key) (uint8_ptr key)
end
