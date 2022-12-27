#include "config.h"

open Unsigned

open AutoConfig2
open SharedDefs
open SharedFunctors
module C = CBytes

type bytes = CBytes.t

module Lib_RandomBuffer_System = Lib_RandomBuffer_System_bindings.Bindings(Lib_RandomBuffer_System_stubs)
module Hacl_Chacha20Poly1305_32 = Hacl_Chacha20Poly1305_32_bindings.Bindings(Hacl_Chacha20Poly1305_32_stubs)
module Hacl_Curve25519_51 = Hacl_Curve25519_51_bindings.Bindings(Hacl_Curve25519_51_stubs)
module Hacl_Ed25519 = Hacl_Ed25519_bindings.Bindings(Hacl_Ed25519_stubs)
module Hacl_SHA3 = Hacl_SHA3_bindings.Bindings(Hacl_SHA3_stubs)
module Hacl_HMAC = Hacl_HMAC_bindings.Bindings(Hacl_HMAC_stubs)
module Hacl_Poly1305_32 = Hacl_Poly1305_32_bindings.Bindings(Hacl_Poly1305_32_stubs)
module Hacl_HKDF = Hacl_HKDF_bindings.Bindings(Hacl_HKDF_stubs)
module Hacl_NaCl = Hacl_NaCl_bindings.Bindings(Hacl_NaCl_stubs)
module Hacl_Hash_Blake2 = Hacl_Hash_Blake2_bindings.Bindings(Hacl_Hash_Blake2_stubs)
module Hacl_Blake2b_32 = Hacl_Hash_Blake2
module Hacl_Blake2s_32 = Hacl_Hash_Blake2
module Hacl_P256 = Hacl_P256_bindings.Bindings(Hacl_P256_stubs)
module Hacl_K256 = Hacl_K256_ECDSA_bindings.Bindings(Hacl_K256_ECDSA_stubs)

#ifdef HACL_CAN_COMPILE_VEC128
module Hacl_Chacha20Poly1305_128 = Hacl_Chacha20Poly1305_128_bindings.Bindings(Hacl_Chacha20Poly1305_128_stubs)
module Hacl_Poly1305_128 = Hacl_Poly1305_128_bindings.Bindings(Hacl_Poly1305_128_stubs)
module Hacl_Blake2s_128 = Hacl_Hash_Blake2s_128_bindings.Bindings(Hacl_Hash_Blake2s_128_stubs)
#endif

#ifdef HACL_CAN_COMPILE_VEC256
module Hacl_Chacha20Poly1305_256 = Hacl_Chacha20Poly1305_256_bindings.Bindings(Hacl_Chacha20Poly1305_256_stubs)
module Hacl_Poly1305_256 = Hacl_Poly1305_256_bindings.Bindings(Hacl_Poly1305_256_stubs)
module Hacl_Blake2b_256 = Hacl_Hash_Blake2b_256_bindings.Bindings(Hacl_Hash_Blake2b_256_stubs)
#endif

#ifdef HACL_CAN_COMPILE_VALE
module Hacl_Curve25519_64 = Hacl_Curve25519_64_bindings.Bindings(Hacl_Curve25519_64_stubs)
#endif

module RandomBuffer = struct
  module Noalloc = struct
    let randombytes ~out =
      Lib_RandomBuffer_System.randombytes (C.ctypes_buf out) (C.size_uint32 out)
  end
  let randombytes ~size =
    let out = C.make size in
    if Noalloc.randombytes ~out then
      Some out
    else
      None
end

module Chacha20_Poly1305_32 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let reqs = []
    let encrypt = Hacl_Chacha20Poly1305_32.hacl_Chacha20Poly1305_32_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_32.hacl_Chacha20Poly1305_32_aead_decrypt
  end)

module Curve25519_51 : Curve25519 =
  Make_Curve25519 (struct
    let reqs = []
    let secret_to_public = Hacl_Curve25519_51.hacl_Curve25519_51_secret_to_public
    let scalarmult = Hacl_Curve25519_51.hacl_Curve25519_51_scalarmult
    let ecdh = Hacl_Curve25519_51.hacl_Curve25519_51_ecdh
  end)

module Ed25519 : EdDSA =
  Make_EdDSA (struct
  let secret_to_public = Hacl_Ed25519.hacl_Ed25519_secret_to_public
  let sign = Hacl_Ed25519.hacl_Ed25519_sign
  let verify = Hacl_Ed25519.hacl_Ed25519_verify
  let expand_keys = Hacl_Ed25519.hacl_Ed25519_expand_keys
  let sign_expanded = Hacl_Ed25519.hacl_Ed25519_sign_expanded
  end)

module SHA2_224 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Agile HashDefs.SHA2_224
    let hash = Hacl_Hash.hacl_Hash_SHA2_hash_224
end)

module SHA2_256 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Agile HashDefs.SHA2_256
    let hash = Hacl_Hash.hacl_Hash_SHA2_hash_256
end)

module SHA2_384 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Agile HashDefs.SHA2_384
    let hash = Hacl_Hash.hacl_Hash_SHA2_hash_384
end)

module SHA2_512 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Agile HashDefs.SHA2_512
    let hash = Hacl_Hash.hacl_Hash_SHA2_hash_512
end)

module SHA3_224 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = SHA3_224
    let hash input input_len output = Hacl_SHA3.hacl_SHA3_sha3_224 input_len input output
end)

module SHA3_256 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = SHA3_256
    let hash input input_len output = Hacl_SHA3.hacl_SHA3_sha3_256 input_len input output
end)

module SHA3_384 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = SHA3_384
    let hash input input_len output = Hacl_SHA3.hacl_SHA3_sha3_384 input_len input output
end)

module SHA3_512 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = SHA3_512
    let hash input input_len output = Hacl_SHA3.hacl_SHA3_sha3_512 input_len input output
end)

module Keccak = struct
  module Noalloc = struct
    let shake128 ~msg ~digest =
      (* Hacl.SHA3.shake128_hacl *)
      assert (C.disjoint msg digest);
      Hacl_SHA3.hacl_SHA3_shake128_hacl (C.size_uint32 msg) (C.ctypes_buf msg) (C.size_uint32 digest) (C.ctypes_buf digest)
    let shake256 ~msg ~digest =
      (* Hacl.SHA3.shake256_hacl *)
      assert (C.disjoint msg digest);
      Hacl_SHA3.hacl_SHA3_shake256_hacl (C.size_uint32 msg) (C.ctypes_buf msg) (C.size_uint32 digest) (C.ctypes_buf digest)
    let keccak ~rate ~capacity ~suffix ~msg ~digest =
      (* Hacl.Impl.SHA3.keccak *)
      assert (rate mod 8 = 0 && rate / 8 > 0 && rate <= 1600);
      assert (capacity + rate = 1600);
      assert (C.disjoint msg digest);
      Hacl_SHA3.hacl_Impl_SHA3_keccak (UInt32.of_int rate) (UInt32.of_int capacity) (C.size_uint32 msg) (C.ctypes_buf msg) (UInt8.of_int suffix) (C.size_uint32 digest) (C.ctypes_buf digest)
  end
  let shake128 ~msg ~size =
    let digest = C.make size in
    Noalloc.shake128 ~msg ~digest;
    digest
  let shake256 ~msg ~size =
    let digest = C.make size in
    Noalloc.shake256 ~msg ~digest;
    digest
  let keccak ~rate ~capacity ~suffix ~msg ~size =
    let digest = C.make size in
    Noalloc.keccak ~rate ~capacity ~suffix ~msg ~digest;
    digest
end

module SHA1 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Agile HashDefs.(Legacy SHA1)
    let hash = Hacl_Hash.hacl_Hash_SHA1_legacy_hash
end) [@@deprecated]

module MD5 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Agile HashDefs.(Legacy MD5)
    let hash = Hacl_Hash.hacl_Hash_MD5_legacy_hash
end) [@@deprecated]

module HMAC_SHA2_256 : MAC =
  Make_HMAC (struct
    let hash_alg = HashDefs.SHA2_256
    let mac = Hacl_HMAC.hacl_HMAC_compute_sha2_256
end)

module HMAC_SHA2_384 : MAC =
  Make_HMAC (struct
    let hash_alg = HashDefs.SHA2_384
    let mac = Hacl_HMAC.hacl_HMAC_compute_sha2_384
end)

module HMAC_SHA2_512 : MAC =
  Make_HMAC (struct
    let hash_alg = HashDefs.SHA2_512
    let mac = Hacl_HMAC.hacl_HMAC_compute_sha2_512
end)

module HMAC_BLAKE2b : MAC =
  Make_HMAC (struct
    let hash_alg = HashDefs.BLAKE2b
    let mac = Hacl_HMAC.hacl_HMAC_compute_blake2b_32
end)

module HMAC_BLAKE2s : MAC =
  Make_HMAC (struct
    let hash_alg = HashDefs.BLAKE2s
    let mac = Hacl_HMAC.hacl_HMAC_compute_blake2s_32
end)

module Poly1305_32 : MAC =
  Make_Poly1305 (struct
    let reqs = []
    let mac = Hacl_Poly1305_32.hacl_Poly1305_32_poly1305_mac
end)

module HKDF_SHA2_256 : HKDF =
  Make_HKDF (struct
    let hash_alg = HashDefs.SHA2_256
    let expand = Hacl_HKDF.hacl_HKDF_expand_sha2_256
    let extract = Hacl_HKDF.hacl_HKDF_extract_sha2_256
  end)

module HKDF_SHA2_512 : HKDF =
  Make_HKDF (struct
    let hash_alg = HashDefs.SHA2_512
    let expand = Hacl_HKDF.hacl_HKDF_expand_sha2_512
    let extract = Hacl_HKDF.hacl_HKDF_extract_sha2_512
  end)

module HKDF_BLAKE2b : HKDF =
  Make_HKDF (struct
    let hash_alg = HashDefs.BLAKE2b
    let expand = Hacl_HKDF.hacl_HKDF_expand_blake2b_32
    let extract = Hacl_HKDF.hacl_HKDF_extract_blake2b_32
  end)

module HKDF_BLAKE2s : HKDF =
  Make_HKDF (struct
    let hash_alg = HashDefs.BLAKE2s
    let expand = Hacl_HKDF.hacl_HKDF_expand_blake2s_32
    let extract = Hacl_HKDF.hacl_HKDF_extract_blake2s_32
  end)

module NaCl = struct
  open Hacl_NaCl

  let tag_len = 16
  let key_len = 32
  let nonce_len = 24
  let get_result r =
    if r = UInt32.zero then
      true
    else
    if r = UInt32.max_int then
      false
    else
      failwith "Unknown return value"
  let check_key_sizes pk sk =
    assert (C.size pk = key_len);
    assert (C.size sk = key_len)
  let check_easy pt ct size_pt size_ct n =
    let open UInt32.Infix in
    assert (size_ct = size_pt + UInt32.of_int tag_len);
    assert (C.size n = nonce_len);
    assert (C.disjoint pt ct);
    assert (C.disjoint n pt);
    assert (C.disjoint n ct)
  let check_detached buf tag n =
    assert (C.size tag = tag_len);
    assert (C.size n = nonce_len);
    assert (C.disjoint tag buf);
    assert (C.disjoint n buf)
  module Noalloc = struct
      let get_sub_buffer buf offset len =
        assert (0 <= offset && offset <= C.size buf);
        let max_len = C.size buf - offset in
        let p = C.ctypes_buf_with_offset buf offset in
        let size = match len with
          | None ->
            UInt32.of_int max_len
          | Some len ->
            assert (0 <= len && len <= max_len);
            UInt32.of_int len
        in
        p, size
    let box_beforenm ~pk ~sk ~ck =
      check_key_sizes pk sk;
      assert (C.size ck = key_len);
      assert (C.disjoint ck pk);
      assert (C.disjoint ck sk);
      get_result @@ hacl_NaCl_crypto_box_beforenm (C.ctypes_buf ck) (C.ctypes_buf pk) (C.ctypes_buf sk)
    module Easy = struct
      let check_and_get_buffers pt pt_offset pt_len ct ct_offset n =
        let p_pt, size_pt = get_sub_buffer pt pt_offset pt_len in
        let p_ct, size_ct = get_sub_buffer ct ct_offset (Option.bind pt_len (fun x -> Some (x + tag_len))) in
        check_easy pt ct size_pt size_ct n;
        p_pt, size_pt, p_ct
      let check_and_get_buffers_open pt pt_offset ct ct_offset ct_len n =
        let p_ct, size_ct = get_sub_buffer ct ct_offset ct_len in
        let p_pt, size_pt = get_sub_buffer pt pt_offset (Option.bind ct_len (fun x -> assert (x >= tag_len); Some (x - tag_len))) in
        check_easy pt ct size_pt size_ct n;
        p_pt, p_ct, size_ct
      let box ~pt ?(pt_offset=0) ?pt_len ~n ~pk ~sk ~ct ?(ct_offset=0) () =
        let p_pt, size_pt, p_ct = check_and_get_buffers pt pt_offset pt_len ct ct_offset n in
        check_key_sizes pk sk;
        get_result @@ hacl_NaCl_crypto_box_easy p_ct p_pt size_pt (C.ctypes_buf n) (C.ctypes_buf pk) (C.ctypes_buf sk)
      let box_open ~ct ?(ct_offset=0) ?ct_len ~n ~pk ~sk ~pt ?(pt_offset=0) () =
        let p_pt, p_ct, size_ct = check_and_get_buffers_open pt pt_offset ct ct_offset ct_len n in
        check_key_sizes pk sk;
        get_result @@ hacl_NaCl_crypto_box_open_easy p_pt p_ct size_ct (C.ctypes_buf n) (C.ctypes_buf pk) (C.ctypes_buf sk)
      let box_afternm ~pt ?(pt_offset=0) ?pt_len ~n ~ck ~ct ?(ct_offset=0) () =
        let p_pt, size_pt, p_ct = check_and_get_buffers pt pt_offset pt_len ct ct_offset n in
        assert (C.size ck = key_len);
        get_result @@ hacl_NaCl_crypto_box_easy_afternm p_ct p_pt size_pt (C.ctypes_buf n) (C.ctypes_buf ck)
      let box_open_afternm ~ct ?(ct_offset=0) ?ct_len ~n ~ck ~pt ?(pt_offset=0) () =
        let p_pt, p_ct, size_ct = check_and_get_buffers_open pt pt_offset ct ct_offset ct_len n in
        assert (C.size ck = key_len);
        get_result @@ hacl_NaCl_crypto_box_open_easy_afternm p_pt p_ct size_ct (C.ctypes_buf n) (C.ctypes_buf ck)
      let secretbox ~pt ?(pt_offset=0) ?pt_len ~n ~key ~ct ?(ct_offset=0) () =
        let p_pt, size_pt, p_ct = check_and_get_buffers pt pt_offset pt_len ct ct_offset n in
        assert (C.size key = key_len);
        get_result @@ hacl_NaCl_crypto_secretbox_easy p_ct p_pt size_pt (C.ctypes_buf n) (C.ctypes_buf key)
      let secretbox_open ~ct ?(ct_offset=0) ?ct_len ~n ~key ~pt ?(pt_offset=0) () =
        let p_pt, p_ct, size_ct = check_and_get_buffers_open pt pt_offset ct ct_offset ct_len n in
        assert (C.size key = key_len);
        get_result @@ hacl_NaCl_crypto_secretbox_open_easy p_pt p_ct size_ct (C.ctypes_buf n) (C.ctypes_buf key)
    end
    module Detached = struct
      let box ~buf ~tag ?(offset=0) ?len ~n ~pk ~sk () =
        check_key_sizes pk sk;
        check_detached buf tag n;
        let p, size = get_sub_buffer buf offset len in
        get_result @@ hacl_NaCl_crypto_box_detached p (C.ctypes_buf tag) p size (C.ctypes_buf n) (C.ctypes_buf pk) (C.ctypes_buf sk)
      let box_open ~buf ~tag ?(offset=0) ?len ~n ~pk ~sk () =
        check_key_sizes pk sk;
        check_detached buf tag n;
        let p, size = get_sub_buffer buf offset len in
        get_result @@ hacl_NaCl_crypto_box_open_detached p p (C.ctypes_buf tag) size (C.ctypes_buf n) (C.ctypes_buf pk) (C.ctypes_buf sk)
      let box_afternm ~buf ~tag ?(offset=0) ?len ~n ~ck () =
        assert (C.size ck = key_len);
        check_detached buf tag n;
        let p, size = get_sub_buffer buf offset len in
        get_result @@ hacl_NaCl_crypto_box_detached_afternm p (C.ctypes_buf tag) p size (C.ctypes_buf n) (C.ctypes_buf ck)
      let box_open_afternm ~buf ~tag ?(offset=0) ?len ~n ~ck () =
        assert (C.size ck = key_len);
        check_detached buf tag n;
        let p, size = get_sub_buffer buf offset len in
        get_result @@ hacl_NaCl_crypto_box_open_detached_afternm p p (C.ctypes_buf tag) size (C.ctypes_buf n) (C.ctypes_buf ck)
      let secretbox ~buf ~tag ?(offset=0) ?len ~n ~key () =
        assert (C.size key = key_len);
        check_detached buf tag n;
        let p, size = get_sub_buffer buf offset len in
        get_result @@ hacl_NaCl_crypto_secretbox_detached p (C.ctypes_buf tag) p size (C.ctypes_buf n) (C.ctypes_buf key)
      let secretbox_open ~buf ~tag ?(offset=0) ?len ~n ~key () =
        assert (C.size key = key_len);
        check_detached buf tag n;
        let p, size = get_sub_buffer buf offset len in
        get_result @@ hacl_NaCl_crypto_secretbox_open_detached p p (C.ctypes_buf tag) size (C.ctypes_buf n) (C.ctypes_buf key)
    end
  end
  let box_beforenm ~pk ~sk =
    let ck = C.make key_len in
    if Noalloc.box_beforenm ~pk ~sk ~ck then
      Some ck
    else
      None
  let box ~pt ~n ~pk ~sk =
    let ct = C.make (C.size pt + tag_len) in
    if Noalloc.Easy.box ~pt ~n ~pk ~sk ~ct () then
      Some ct
    else
      None
  let box_open ~ct ~n ~pk ~sk =
    assert (C.size ct >= tag_len);
    let pt = C.make (C.size ct - tag_len) in
    if Noalloc.Easy.box_open ~ct ~n ~pk ~sk ~pt () then
      Some pt
    else
      None
  let box_afternm ~pt ~n ~ck =
    let ct = C.make (C.size pt + tag_len) in
    if Noalloc.Easy.box_afternm ~pt ~n ~ck ~ct () then
      Some ct
    else
      None
  let box_open_afternm ~ct ~n ~ck =
    assert (C.size ct >= tag_len);
    let pt = C.make (C.size ct - tag_len) in
    if Noalloc.Easy.box_open_afternm ~ct ~n ~ck ~pt () then
      Some pt
    else
      None
  let secretbox ~pt ~n ~key =
    let ct = C.make (C.size pt + tag_len) in
    if Noalloc.Easy.secretbox ~pt ~n ~key ~ct () then
      Some ct
    else
      None
  let secretbox_open ~ct ~n ~key =
    assert (C.size ct >= tag_len);
    let pt = C.make (C.size ct - tag_len) in
    if Noalloc.Easy.secretbox_open ~ct ~n ~key ~pt () then
      Some pt
    else
      None
end

module P256 = struct
  module NoHash = Make_ECDSA (struct
      let min_msg_size = 32
      let sign = Hacl_P256.hacl_P256_ecdsa_sign_p256_without_hash
      let verify = Hacl_P256.hacl_P256_ecdsa_verif_without_hash
    end)
  module Noalloc = struct
    let raw_to_compressed ~p ~result =
      (* Hacl.P256.raw_to_compressed *)
      assert (C.size p = 64);
      assert (C.size result = 33);
      Hacl_P256.hacl_P256_raw_to_compressed (C.ctypes_buf p) (C.ctypes_buf result)
    let raw_to_uncompressed ~p ~result =
      (* Hacl.P256.raw_to_uncompressed *)
      assert (C.size p = 64);
      assert (C.size result = 65);
      Hacl_P256.hacl_P256_raw_to_uncompressed (C.ctypes_buf p) (C.ctypes_buf result)
    let compressed_to_raw ~p ~result =
      (* Hacl.P256.compressed_to_raw *)
      assert (C.size p = 33);
      assert (C.size result = 64);
      Hacl_P256.hacl_P256_compressed_to_raw (C.ctypes_buf p) (C.ctypes_buf result)
    let uncompressed_to_raw ~p ~result =
      (* Hacl.P256.uncompressed_to_raw *)
      assert (C.size p = 65);
      assert (C.size result = 64);
      Hacl_P256.hacl_P256_uncompressed_to_raw (C.ctypes_buf p) (C.ctypes_buf result)
    let dh_initiator ~sk ~pk =
      (* Hacl.P256.dh_initiator *)
      assert (C.size pk = 64);
      assert (C.size sk = 32);
      assert (C.disjoint pk sk);
      Hacl_P256.hacl_P256_dh_initiator (C.ctypes_buf pk) (C.ctypes_buf sk)
    let dh_responder ~sk ~pk ~shared =
      (* Hacl.P256.dh_responder *)
      assert (C.size shared = 64);
      assert (C.size pk = 64);
      assert (C.size sk = 32);
      assert (C.disjoint shared sk);
      assert (C.disjoint shared pk);
      Hacl_P256.hacl_P256_dh_responder (C.ctypes_buf shared) (C.ctypes_buf pk) (C.ctypes_buf sk)
    let sign = NoHash.Noalloc.sign
  end
  let raw_to_compressed p =
    let result = C.make 33 in
    Noalloc.raw_to_compressed ~p ~result;
    result
  let raw_to_uncompressed p =
    let result = C.make 65 in
    Noalloc.raw_to_uncompressed ~p ~result;
    result
  let compressed_to_raw p =
    let result = C.make 64 in
    if Noalloc.compressed_to_raw ~p ~result then
      Some result
    else
      None
  let uncompressed_to_raw p =
    let result = C.make 64 in
    if Noalloc.uncompressed_to_raw ~p ~result then
      Some result
    else
      None
  let dh_initiator ~sk =
    let pk = C.make 64 in
    if Noalloc.dh_initiator ~sk ~pk then
      Some pk
    else
      None
  let dh_responder ~sk ~pk  =
    let shared = C.make 64 in
    if Noalloc.dh_responder ~sk ~pk ~shared then
      Some shared
    else
      None
  let valid_sk ~sk =
    (* Hacl.P256.validate_private_key *)
    assert (C.size sk = 32);
    Hacl_P256.hacl_P256_validate_private_key (C.ctypes_buf sk)
  let valid_pk ~pk =
    (* Hacl.P256.validate_public_key *)
    assert (C.size pk = 64);
    Hacl_P256.hacl_P256_validate_public_key (C.ctypes_buf pk)
  let sign = NoHash.sign
  let verify = NoHash.verify
  module SHA2_256 = Make_ECDSA (struct
      let min_msg_size = 0
      let sign = Hacl_P256.hacl_P256_ecdsa_sign_p256_sha2
      let verify = Hacl_P256.hacl_P256_ecdsa_verif_p256_sha2
    end)
  module SHA2_384 = Make_ECDSA (struct
      let min_msg_size = 0
      let sign = Hacl_P256.hacl_P256_ecdsa_sign_p256_sha384
      let verify = Hacl_P256.hacl_P256_ecdsa_verif_p256_sha384
    end)
  module SHA2_512 = Make_ECDSA (struct
      let min_msg_size = 0
      let sign = Hacl_P256.hacl_P256_ecdsa_sign_p256_sha512
      let verify = Hacl_P256.hacl_P256_ecdsa_verif_p256_sha512
    end)
end

module K256 = struct
  let k256_group_order = Z.of_string "115792089237316195423570985008687907852837564279074904382605163141518161494337"
  let size_signature = 64
  let size_pk = 64
  let size_pk_uncompressed = 65
  let size_pk_compressed = 33
  let size_sk = 32
  let size_hashed_msg = 32
  let valid_sk ~sk =
    C.size sk = size_sk && C.z_compare sk Z.zero > 0 && C.z_compare sk k256_group_order < 0
  module Noalloc = struct
    let raw_to_compressed ~p ~result =
      (* Hacl.K256.ECDSA.public_key_compressed_from_raw *)
      assert (C.size p = size_pk);
      assert (C.size result = size_pk_compressed);
      Hacl_K256.hacl_K256_ECDSA_public_key_compressed_from_raw (C.ctypes_buf result) (C.ctypes_buf p)
    let raw_to_uncompressed ~p ~result =
      (* Hacl.K256.ECDSA.public_key_uncompressed_from_raw *)
      assert (C.size p = size_pk);
      assert (C.size result = size_pk_uncompressed);
      Hacl_K256.hacl_K256_ECDSA_public_key_uncompressed_from_raw (C.ctypes_buf result) (C.ctypes_buf p)
    let compressed_to_raw ~p ~result =
      (* Hacl.K256.ECDSA.public_key_compressed_to_raw *)
      assert (C.size p = size_pk_compressed);
      assert (C.size result = size_pk);
      Hacl_K256.hacl_K256_ECDSA_public_key_compressed_to_raw (C.ctypes_buf result) (C.ctypes_buf p)
    let uncompressed_to_raw ~p ~result =
      (* Hacl.K256.ECDSA.public_key_uncompressed_to_raw *)
      assert (C.size p = size_pk_uncompressed);
      assert (C.size result = size_pk);
      Hacl_K256.hacl_K256_ECDSA_public_key_uncompressed_to_raw (C.ctypes_buf result) (C.ctypes_buf p)
    let secret_to_public ~sk ~pk =
      (* Hacl.K256.ECDSA.secret_to_public *)
      assert (C.size sk = size_sk);
      assert (C.size pk = size_pk);
      Hacl_K256.hacl_K256_ECDSA_secret_to_public (C.ctypes_buf pk) (C.ctypes_buf sk)
    let sign ~sk ~msg ~k ~signature =
      (* Hacl.K256.ECDSA.ecdsa_sign_hashed_msg *)
      assert (C.size signature = size_signature);
      assert (valid_sk ~sk);
      assert (valid_sk ~sk:k);
      assert (C.size msg = size_hashed_msg);
      Hacl_K256.hacl_K256_ECDSA_ecdsa_sign_hashed_msg
        (C.ctypes_buf signature) (C.ctypes_buf msg) (C.ctypes_buf sk) (C.ctypes_buf k)
    module Libsecp256k1 = struct
      let normalize_signature ~signature =
        (* Hacl.K256.ECDSA.secp256k1_ecdsa_signature_normalize *)
        assert (C.size signature = size_signature);
        Hacl_K256.hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize (C.ctypes_buf signature)
      let sign ~sk ~msg ~k ~signature =
        (* Hacl.K256.ECDSA.secp256k1_ecdsa_sign_hashed_msg *)
        assert (C.size signature = size_signature);
        assert (valid_sk ~sk);
        assert (valid_sk ~sk:k);
        assert (C.size msg = size_hashed_msg);
        Hacl_K256.hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg
          (C.ctypes_buf signature) (C.ctypes_buf msg) (C.ctypes_buf sk) (C.ctypes_buf k)
    end
  end
  let valid_pk ~pk =
    (* Hacl.K256.ECDSA.is_public_key_valid *)
    assert (C.size pk = size_pk);
    Hacl_K256.hacl_K256_ECDSA_is_public_key_valid (C.ctypes_buf pk)
  let secret_to_public ~sk =
    let pk = C.make size_pk in
    if Noalloc.secret_to_public ~sk ~pk then
      Some pk
    else
      None
  let sign ~sk ~msg ~k =
    let signature = C.make size_signature in
    if Noalloc.sign ~sk ~msg ~k ~signature then
      Some signature
    else
      None
  let verify ~pk ~msg ~signature =
    (* Hacl.K256.ECDSA.ecdsa_verify_hashed_msg *)
    assert (C.size msg = size_hashed_msg);
    assert (C.size pk = size_pk);
    assert (C.size signature = size_signature);
    Hacl_K256.hacl_K256_ECDSA_ecdsa_verify_hashed_msg
      (C.ctypes_buf msg) (C.ctypes_buf pk) (C.ctypes_buf signature)
  module Libsecp256k1 = struct
    let sign ~sk ~msg ~k =
      let signature = C.make 64 in
      if Noalloc.Libsecp256k1.sign ~sk ~msg ~k ~signature then
        Some signature
      else
        None
    let verify ~pk ~msg ~signature =
      (* Hacl.K256.ECDSA.secp256k1_ecdsa_verify_hashed_msg *)
      assert (C.size msg = size_hashed_msg);
      assert (C.size pk = size_pk);
      assert (C.size signature = size_signature);
      Hacl_K256.hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg
        (C.ctypes_buf msg) (C.ctypes_buf pk) (C.ctypes_buf signature)
    let is_signature_normalized ~signature =
      (* Hacl.K256.ECDSA.secp256k1_ecdsa_is_signature_normalized *)
      assert (C.size signature = size_signature);
        Hacl_K256.hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized (C.ctypes_buf signature)
    let normalize_signature ~signature =
      if Noalloc.Libsecp256k1.normalize_signature ~signature then
        Some (Bytes.copy signature)
      else
        None
  end
  let raw_to_compressed p =
    let result = C.make size_pk_compressed in
    Noalloc.raw_to_compressed ~p ~result;
    result
  let raw_to_uncompressed p =
    let result = C.make size_pk_uncompressed in
    Noalloc.raw_to_uncompressed ~p ~result;
    result
  let compressed_to_raw p =
    let result = C.make size_pk in
    if Noalloc.compressed_to_raw ~p ~result then
      Some result
    else
      None
  let uncompressed_to_raw p =
    let result = C.make size_pk in
    if Noalloc.uncompressed_to_raw ~p ~result then
      Some result
    else
      None
end

module Blake2b_32 : Blake2 =
  Make_Blake2b (struct
    let reqs = []
    let blake2b = Hacl_Blake2b_32.hacl_Blake2b_32_blake2b
  end)

module Blake2s_32 : Blake2 =
  Make_Blake2s (struct
    let reqs = []
    let blake2s = Hacl_Blake2s_32.hacl_Blake2s_32_blake2s
  end)

#ifdef HACL_CAN_COMPILE_VEC128
module Chacha20_Poly1305_128 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let reqs = [VEC128]
    let encrypt = Hacl_Chacha20Poly1305_128.hacl_Chacha20Poly1305_128_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_128.hacl_Chacha20Poly1305_128_aead_decrypt
  end)

module Poly1305_128 : MAC =
  Make_Poly1305 (struct
    let reqs = [VEC128]
    let mac = Hacl_Poly1305_128.hacl_Poly1305_128_poly1305_mac
end)

module Blake2s_128 : Blake2 =
  Make_Blake2s (struct
    let reqs = [VEC128]
    let blake2s = Hacl_Blake2s_128.hacl_Blake2s_128_blake2s
  end)
#else
module Chacha20_Poly1305_128 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let reqs = [VEC128]
    let encrypt _ _ _ _ _ _ = failwith "Not implemented on this platform"
    let decrypt _ _ _ _ _ _ = failwith "Not implemented on this platform"
  end)

module Poly1305_128 : MAC =
  Make_Poly1305 (struct
    let reqs = [VEC128]
    let mac _ _ _ = failwith "Not implemented on this platform"
end)

module Blake2s_128 : Blake2 =
  Make_Blake2s (struct
    let reqs = [VEC128]
    let blake2s _ _ _ = failwith "Not implemented on this platform"
  end)
#endif

#ifdef HACL_CAN_COMPILE_VEC256
module Chacha20_Poly1305_256 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let reqs = [VEC256]
    let encrypt = Hacl_Chacha20Poly1305_256.hacl_Chacha20Poly1305_256_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_256.hacl_Chacha20Poly1305_256_aead_decrypt
  end)

module Poly1305_256 : MAC =
  Make_Poly1305 (struct
      let reqs = [VEC256]
    let mac = Hacl_Poly1305_256.hacl_Poly1305_256_poly1305_mac
end)

module Blake2b_256 : Blake2 =
  Make_Blake2b (struct
    let reqs = [VEC256]
    let blake2b = Hacl_Blake2b_256.hacl_Blake2b_256_blake2b
  end)
#else
module Chacha20_Poly1305_256 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
     let reqs = [VEC256]
    let encrypt _ _ _ _ _ _ = failwith "Not implemented on this platform"
    let decrypt _ _ _ _ _ _ = failwith "Not implemented on this platform"
  end)

module Poly1305_256 : MAC =
  Make_Poly1305 (struct
      let reqs = [VEC256]
    let mac _ _ _ = failwith "Not implemented on this platform"
end)

module Blake2b_256 : Blake2 =
  Make_Blake2b (struct
    let reqs = [VEC256]
    let blake2b _ _ _ = failwith "Not implemented on this platform"
  end)
#endif

#ifdef HACL_CAN_COMPILE_VALE

module Curve25519_64 : Curve25519 =
  Make_Curve25519 (struct
    let reqs = [BMI2; ADX]
    let secret_to_public = Hacl_Curve25519_64.hacl_Curve25519_64_secret_to_public
    let scalarmult = Hacl_Curve25519_64.hacl_Curve25519_64_scalarmult
    let ecdh = Hacl_Curve25519_64.hacl_Curve25519_64_ecdh
  end)
#else

module Curve25519_64 : Curve25519 =
  Make_Curve25519 (struct
    let reqs = [BMI2; ADX]
    let secret_to_public _ _ = failwith "Not implemented on this platform"
    let scalarmult _ _ _ = failwith "Not implemented on this platform"
    let ecdh _ _ _ = failwith "Not implemented on this platform"
  end)

#endif
