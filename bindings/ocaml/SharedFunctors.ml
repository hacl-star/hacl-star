open Unsigned

open SharedDefs

module Make_Chacha20_Poly1305_generic (C: Buffer)
    (Impl : sig
       val encrypt : C.buf -> C.buf -> uint32 -> C.buf -> uint32 -> C.buf -> C.buf -> C.buf -> unit
       val decrypt : C.buf -> C.buf -> uint32 -> C.buf -> uint32 -> C.buf -> C.buf -> C.buf -> uint32
     end)
= struct
  type t = C.t
  let encrypt key iv ad pt ct tag =
    Impl.encrypt (C.ctypes_buf key) (C.ctypes_buf iv) (C.size_uint32 ad) (C.ctypes_buf ad)
      (C.size_uint32 pt) (C.ctypes_buf pt) (C.ctypes_buf ct) (C.ctypes_buf tag)

  let decrypt key iv ad pt ct tag =
    let result = Impl.decrypt (C.ctypes_buf key) (C.ctypes_buf iv) (C.size_uint32 ad) (C.ctypes_buf ad)
        (C.size_uint32 pt) (C.ctypes_buf pt) (C.ctypes_buf ct) (C.ctypes_buf tag)
    in
    UInt32.to_int result = 0
end

module Make_Curve25519_generic (C: Buffer)
    (Impl : sig
    val secret_to_public : C.buf -> C.buf -> unit
    val scalarmult : C.buf -> C.buf -> C.buf -> unit
    val ecdh : C.buf -> C.buf -> C.buf -> bool
  end)
= struct
  type t = C.t
  let secret_to_public pub priv =
    assert (C.disjoint pub priv);
    assert (C.size pub = 32);
    assert (C.size priv = 32);
    Impl.secret_to_public (C.ctypes_buf pub) (C.ctypes_buf priv)
  let scalarmult shared my_priv their_pub =
    assert (C.disjoint shared my_priv);
    assert (C.disjoint shared their_pub);
    assert (C.size shared = 32);
    assert (C.size my_priv = 32);
    assert (C.size their_pub = 32);
    Impl.scalarmult (C.ctypes_buf shared) (C.ctypes_buf my_priv) (C.ctypes_buf their_pub)
  let ecdh shared my_priv their_pub =
    assert (C.disjoint shared my_priv);
    assert (C.disjoint shared their_pub);
    assert (C.size shared = 32);
    assert (C.size my_priv = 32);
    assert (C.size their_pub = 32);
    Impl.ecdh (C.ctypes_buf shared) (C.ctypes_buf my_priv) (C.ctypes_buf their_pub)
end

module Make_EdDSA_generic (C: Buffer)
    (Impl : sig
  val secret_to_public : C.buf -> C.buf -> unit
  val sign : C.buf -> C.buf -> uint32 -> C.buf -> unit
  val verify : C.buf -> uint32 -> C.buf -> C.buf -> bool
  val expand_keys : C.buf -> C.buf -> unit
  val sign_expanded : C.buf -> C.buf -> uint32 -> C.buf -> unit
  end)
= struct
  type t = C.t
  let secret_to_public pub priv = Impl.secret_to_public (C.ctypes_buf pub) (C.ctypes_buf priv)
  let sign signature priv msg = Impl.sign (C.ctypes_buf signature) (C.ctypes_buf priv) (C.size_uint32 msg) (C.ctypes_buf msg)
  let verify pub msg signature = Impl.verify (C.ctypes_buf pub) (C.size_uint32 msg) (C.ctypes_buf msg) (C.ctypes_buf signature)
  let expand_keys ks priv = Impl.expand_keys (C.ctypes_buf ks) (C.ctypes_buf priv)
  let sign_expanded signature ks msg = Impl.sign_expanded (C.ctypes_buf signature) (C.ctypes_buf ks) (C.size_uint32 msg) (C.ctypes_buf msg)
end

module Make_HashFunction_generic (C: Buffer)
    (Impl : sig
       val hash_alg : HashDefs.alg option
       val hash : C.buf -> uint32 -> C.buf -> unit
     end)
= struct
  type t = C.t
  let hash input output =
    HashDefs.check_digest_len Impl.hash_alg (C.size output);
    assert (C.disjoint input output);
    Impl.hash (C.ctypes_buf input) (C.size_uint32 input) (C.ctypes_buf output)
end

module Make_Poly1305_generic (C: Buffer)
    (Impl : sig
       val mac : C.buf -> uint32 -> C.buf -> C.buf -> unit
     end)
= struct
  type t = C.t
  let mac dst key data = Impl.mac (C.ctypes_buf dst) (C.size_uint32 data) (C.ctypes_buf data) (C.ctypes_buf key)
end

module Make_HMAC_generic (C: Buffer)
    (Impl : sig
       val hash_alg : HashDefs.alg
       val mac : C.buf -> C.buf -> uint32 -> C.buf -> uint32 -> unit
  end)
= struct
  type t = C.t
  let mac dst key data =
    assert (HashDefs.digest_len Impl.hash_alg = C.size dst);
    assert (C.disjoint dst key);
    Impl.mac (C.ctypes_buf dst) (C.ctypes_buf key) (C.size_uint32 key) (C.ctypes_buf data) (C.size_uint32 data)
end

module Make_HKDF_generic (C: Buffer)
    (Impl: sig
       val hash_alg : HashDefs.alg
       val expand : C.buf -> C.buf -> uint32 -> C.buf -> uint32 -> uint32 -> unit
       val extract : C.buf -> C.buf -> uint32 -> C.buf -> uint32 -> unit
     end)
= struct
  type t = C.t
  let expand okm prk info =
    assert (C.size okm <= 255 * HashDefs.digest_len Impl.hash_alg);
    assert (HashDefs.digest_len Impl.hash_alg <= C.size prk);
    assert (C.disjoint okm prk);
    Impl.expand (C.ctypes_buf okm) (C.ctypes_buf prk) (C.size_uint32 prk) (C.ctypes_buf info) (C.size_uint32 info) (C.size_uint32 okm)
  let extract prk salt ikm =
    assert (C.size prk = HashDefs.digest_len Impl.hash_alg);
    assert (C.disjoint salt prk);
    assert (C.disjoint ikm prk);
    Impl.extract (C.ctypes_buf prk) (C.ctypes_buf salt) (C.size_uint32 salt) (C.ctypes_buf ikm) (C.size_uint32 ikm)
end

module Make_Blake2b_generic (C: Buffer)
    (Impl : sig
       val blake2b : uint32 -> C.buf -> uint32 -> C.buf -> uint32 -> C.buf -> unit
     end)
= struct
  type t = C.t
  let hash key pt output = Impl.blake2b (C.size_uint32 output) (C.ctypes_buf output) (C.size_uint32 pt) (C.ctypes_buf pt) (C.size_uint32 key) (C.ctypes_buf key)
end

module Make_Chacha20_Poly1305 = Make_Chacha20_Poly1305_generic (CBytes)
module Make_Curve25519 = Make_Curve25519_generic (CBytes)
module Make_EdDSA = Make_EdDSA_generic (CBytes)
module Make_HashFunction = Make_HashFunction_generic (CBytes)
module Make_Poly1305 = Make_Poly1305_generic (CBytes)
module Make_HMAC = Make_HMAC_generic (CBytes)
module Make_HKDF = Make_HKDF_generic (CBytes)
module Make_Blake2b = Make_Blake2b_generic (CBytes)
