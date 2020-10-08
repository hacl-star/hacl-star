open Unsigned

open SharedDefs
open AutoConfig2

let check_reqs = List.iter (fun x -> assert (has_feature x))

module Make_Chacha20_Poly1305_generic (C: Buffer)
    (Impl : sig
       val reqs : feature list
       val encrypt : C.buf -> C.buf -> uint32 -> C.buf -> uint32 -> C.buf -> C.buf -> C.buf -> unit
       val decrypt : C.buf -> C.buf -> uint32 -> C.buf -> uint32 -> C.buf -> C.buf -> C.buf -> uint32
     end)
= struct
  type t = C.t
  let check_sizes key iv tag =
    assert (C.size key = 32);
    assert (C.size iv = 12);
    assert (C.size tag = 16)
  let encrypt key iv ad pt ct tag =
    check_reqs Impl.reqs;
    (* Hacl.Impl.Chacha20Poly1305.aead_encrypt_st *)
    check_sizes key iv tag;
    assert (C.disjoint key ct);
    assert (C.disjoint iv ct);
    assert (C.disjoint key tag);
    assert (C.disjoint iv tag);
    assert (C.disjoint ct tag);
    assert (C.disjoint ad ct);
    Impl.encrypt (C.ctypes_buf key) (C.ctypes_buf iv) (C.size_uint32 ad) (C.ctypes_buf ad)
      (C.size_uint32 pt) (C.ctypes_buf pt) (C.ctypes_buf ct) (C.ctypes_buf tag)
  let decrypt key iv ad pt ct tag =
    check_reqs Impl.reqs;
    (* Hacl.Impl.Chacha20Poly1305.aead_decrypt_st *)
    check_sizes key iv tag;
    let result = Impl.decrypt (C.ctypes_buf key) (C.ctypes_buf iv) (C.size_uint32 ad) (C.ctypes_buf ad)
        (C.size_uint32 pt) (C.ctypes_buf pt) (C.ctypes_buf ct) (C.ctypes_buf tag)
    in
    UInt32.to_int result = 0
end

module Make_Curve25519_generic (C: Buffer)
    (Impl : sig
       val reqs : feature list
       val secret_to_public : C.buf -> C.buf -> unit
       val scalarmult : C.buf -> C.buf -> C.buf -> unit
       val ecdh : C.buf -> C.buf -> C.buf -> bool
  end)
= struct
  type t = C.t
  let secret_to_public pub priv =
    check_reqs Impl.reqs;
    (* Hacl.Impl.Curve25519.Generic.secret_to_public_st *)
    assert (C.disjoint pub priv);
    assert (C.size pub = 32);
    assert (C.size priv = 32);
    Impl.secret_to_public (C.ctypes_buf pub) (C.ctypes_buf priv)
  let scalarmult shared my_priv their_pub =
    check_reqs Impl.reqs;
    (* Hacl.Impl.Curve25519.Generic.scalarmult_st *)
    assert (C.disjoint shared my_priv);
    assert (C.disjoint shared their_pub);
    assert (C.size shared = 32);
    assert (C.size my_priv = 32);
    assert (C.size their_pub = 32);
    Impl.scalarmult (C.ctypes_buf shared) (C.ctypes_buf my_priv) (C.ctypes_buf their_pub)
  let ecdh shared my_priv their_pub =
    check_reqs Impl.reqs;
    (* Hacl.Impl.Curve25519.Generic.ecdh_st *)
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
  let secret_to_public pub priv =
    (* Hacl.Ed25519.secret_to_public *)
    assert (C.size pub = 32);
    assert (C.size priv = 32);
    assert (C.disjoint pub priv);
    Impl.secret_to_public (C.ctypes_buf pub) (C.ctypes_buf priv)
  let sign signature priv msg =
    (* Hacl.Ed25519.sign *)
    assert (C.size priv = 32);
    assert (C.size signature = 64);
    assert Z.(of_int (C.size msg) + ~$64 <= max_size_t);
    Impl.sign (C.ctypes_buf signature) (C.ctypes_buf priv) (C.size_uint32 msg) (C.ctypes_buf msg)
  let verify pub msg signature =
    (* Hacl.Ed25519.verify *)
    assert (C.size pub = 32);
    assert (C.size signature = 64);
    assert Z.(of_int (C.size msg) + ~$64 <= max_size_t);
    Impl.verify (C.ctypes_buf pub) (C.size_uint32 msg) (C.ctypes_buf msg) (C.ctypes_buf signature)
  let expand_keys ks priv =
    (* Hacl.Ed25519.expand_keys *)
    assert (C.size ks = 96);
    assert (C.size priv = 32);
    assert (C.disjoint ks priv); (* VD: redundant for Bytes, since size is different *)
    Impl.expand_keys (C.ctypes_buf ks) (C.ctypes_buf priv)
  let sign_expanded signature ks msg =
    (* Hacl.Ed25519.sign_expanded *)
    assert (C.size ks = 96);
    assert (C.size signature = 64);
    assert Z.(of_int (C.size msg) + ~$64 <= max_size_t);
    Impl.sign_expanded (C.ctypes_buf signature) (C.ctypes_buf ks) (C.size_uint32 msg) (C.ctypes_buf msg)
end

module Make_HashFunction_generic (C: Buffer)
    (Impl : sig
       val hash_alg : HashDefs.alg option
       val hash : C.buf -> uint32 -> C.buf -> unit
     end)
= struct
  type t = C.t
  let hash input output =
    HashDefs.check_max_input_len (C.size input);
    assert (C.disjoint input output);
    HashDefs.check_digest_len Impl.hash_alg (C.size output);
    Impl.hash (C.ctypes_buf input) (C.size_uint32 input) (C.ctypes_buf output)
end

module Make_Poly1305_generic (C: Buffer)
    (Impl : sig
       val reqs : feature list
       val mac : C.buf -> uint32 -> C.buf -> C.buf -> unit
     end)
= struct
  type t = C.t
  let mac dst key data =
    check_reqs Impl.reqs;
    (* Hacl.Impl.Poly1305.poly1305_mac_st *)
    assert (C.size dst = 16);
    assert (C.size key = 32);
    assert (C.disjoint dst data);
    assert (C.disjoint key data);
    Impl.mac (C.ctypes_buf dst) (C.size_uint32 data) (C.ctypes_buf data) (C.ctypes_buf key)
end

module Make_HMAC_generic (C: Buffer)
    (Impl : sig
       val hash_alg : HashDefs.alg
       val mac : C.buf -> C.buf -> uint32 -> C.buf -> uint32 -> unit
  end)
= struct
  type t = C.t
  let mac dst key data =
    (* Hacl.HMAC.compute_st *)
    assert (HashDefs.digest_len Impl.hash_alg = C.size dst);
    assert (C.disjoint dst key);
    HashDefs.check_key_len Impl.hash_alg (C.size key);
    HashDefs.check_key_len Impl.hash_alg (C.size data);
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
    (* Hacl.HKDF.expand_st *)
    assert (C.size okm <= 255 * HashDefs.digest_len Impl.hash_alg);
    assert (C.disjoint okm prk);
    assert (HashDefs.digest_len Impl.hash_alg <= C.size prk);
    HashDefs.(check_max_input_len (digest_len Impl.hash_alg + block_len Impl.hash_alg + C.size info + 1));
    HashDefs.check_key_len Impl.hash_alg (C.size prk);
    Impl.expand (C.ctypes_buf okm) (C.ctypes_buf prk) (C.size_uint32 prk) (C.ctypes_buf info) (C.size_uint32 info) (C.size_uint32 okm)
  let extract prk salt ikm =
    (* Hacl.HKDF.extract_st *)
    assert (C.size prk = HashDefs.digest_len Impl.hash_alg);
    assert (C.disjoint salt prk);
    assert (C.disjoint ikm prk);
    HashDefs.check_key_len Impl.hash_alg (C.size salt);
    HashDefs.check_key_len Impl.hash_alg (C.size ikm);
    Impl.extract (C.ctypes_buf prk) (C.ctypes_buf salt) (C.size_uint32 salt) (C.ctypes_buf ikm) (C.size_uint32 ikm)
end

module Make_ECDSA_generic (C: Buffer)
    (Impl : sig
       val min_msg_size : int
       val sign : C.buf -> uint32 -> C.buf -> C.buf -> C.buf -> bool
       val verify : uint32 -> C.buf -> C.buf -> C.buf -> C.buf -> bool
     end)
= struct
  type t = C.t
  let get_result r =
    if r = UInt64.zero then
      true
    else
    if r = UInt64.max_int then
      false
    else
      failwith "Unknown return value"
  let prime_p256_order = Z.of_string "115792089210356248762697446949407573529996955224135760342422259061068512044369"
  let sign priv msg k signature =
    (* Hacl.Interface.P256.ECDSA.ecdsa_sign_p256_without_hash/sha2/sha384 *)
    assert (C.size signature = 64);
    assert (C.size priv = 32);
    assert (C.size k = 32);
    assert (C.size msg >= Impl.min_msg_size);
    assert (C.disjoint signature msg);
    assert (C.z_compare priv prime_p256_order < 0);
    assert (C.z_compare k prime_p256_order < 0);
    Impl.sign (C.ctypes_buf signature) (C.size_uint32 msg) (C.ctypes_buf msg) (C.ctypes_buf priv) (C.ctypes_buf k)
  let verify pub msg signature =
    (* Hacl.Interface.P256.ECDSA.ecdsa_verif_without_hash/sha2/sha384 *)
    assert (C.size signature = 64);
    assert (C.size pub = 64);
    assert (C.size msg >= Impl.min_msg_size);
    let r, s = C.sub signature 0 32, C.sub signature 32 32 in
    Impl.verify (C.size_uint32 msg) (C.ctypes_buf msg) (C.ctypes_buf pub) (C.ctypes_buf r) (C.ctypes_buf s)
end


module Make_Blake2b_generic (C: Buffer)
    (Impl : sig
       val reqs : feature list
       val blake2b : uint32 -> C.buf -> uint32 -> C.buf -> uint32 -> C.buf -> unit
     end)
= struct
  type t = C.t
  let hash key pt output =
    check_reqs Impl.reqs;
    (* Hacl.Impl.Blake2.Generic.blake2_t *)
    assert (C.size output > 0 && C.size output <= 64);
    assert (C.size key <= 64);
    if C.size key = 0 then
      assert Z.(of_int (C.size pt) <= max_size_t)
    else
      assert Z.(of_int (C.size pt) + ~$1024 <= max_size_t);
    assert (C.disjoint key pt);
    assert (C.disjoint key output);
    assert (C.disjoint pt output);
    Impl.blake2b (C.size_uint32 output) (C.ctypes_buf output) (C.size_uint32 pt) (C.ctypes_buf pt) (C.size_uint32 key) (C.ctypes_buf key)
end

module Make_Blake2s_generic (C: Buffer)
    (Impl : sig
       val reqs : feature list
       val blake2s : uint32 -> C.buf -> uint32 -> C.buf -> uint32 -> C.buf -> unit
     end)
= struct
  type t = C.t
  let hash key pt output =
    check_reqs Impl.reqs;
    (* Hacl.Impl.Blake2.Generic.blake2_t *)
    assert (C.size output > 0 && C.size output <= 32);
    assert (C.size key <= 32);
    if C.size key = 0 then
      assert Z.(of_int (C.size pt) <= max_size_t)
    else
      assert Z.(of_int (C.size pt) + ~$512 <= max_size_t);
    assert (C.disjoint key pt);
    assert (C.disjoint key output);
    assert (C.disjoint pt output);
    Impl.blake2s (C.size_uint32 output) (C.ctypes_buf output) (C.size_uint32 pt) (C.ctypes_buf pt) (C.size_uint32 key) (C.ctypes_buf key)
end

module Make_Chacha20_Poly1305 = Make_Chacha20_Poly1305_generic (CBytes)
module Make_Curve25519 = Make_Curve25519_generic (CBytes)
module Make_EdDSA = Make_EdDSA_generic (CBytes)
module Make_HashFunction = Make_HashFunction_generic (CBytes)
module Make_Poly1305 = Make_Poly1305_generic (CBytes)
module Make_HMAC = Make_HMAC_generic (CBytes)
module Make_HKDF = Make_HKDF_generic (CBytes)
module Make_ECDSA = Make_ECDSA_generic (CBytes)
module Make_Blake2b = Make_Blake2b_generic (CBytes)
module Make_Blake2s = Make_Blake2s_generic (CBytes)
