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
module Hacl_Hash = Hacl_Hash_bindings.Bindings(Hacl_Hash_stubs)
module Hacl_SHA3 = Hacl_SHA3_bindings.Bindings(Hacl_SHA3_stubs)
module Hacl_HMAC = Hacl_HMAC_bindings.Bindings(Hacl_HMAC_stubs)
module Hacl_Poly1305_32 = Hacl_Poly1305_32_bindings.Bindings(Hacl_Poly1305_32_stubs)
module Hacl_HKDF = Hacl_HKDF_bindings.Bindings(Hacl_HKDF_stubs)
module Hacl_NaCl = Hacl_NaCl_bindings.Bindings(Hacl_NaCl_stubs)
module Hacl_Blake2b_32 = Hacl_Blake2b_32_bindings.Bindings(Hacl_Blake2b_32_stubs)
module Hacl_Blake2s_32 = Hacl_Blake2s_32_bindings.Bindings(Hacl_Blake2s_32_stubs)
module Hacl_P256 = Hacl_P256_bindings.Bindings(Hacl_P256_stubs)

#if not (defined IS_NOT_X64) || defined IS_ARM_8
module Hacl_Chacha20Poly1305_128 = Hacl_Chacha20Poly1305_128_bindings.Bindings(Hacl_Chacha20Poly1305_128_stubs)
module Hacl_Poly1305_128 = Hacl_Poly1305_128_bindings.Bindings(Hacl_Poly1305_128_stubs)
module Hacl_Blake2s_128 = Hacl_Blake2s_128_bindings.Bindings(Hacl_Blake2s_128_stubs)
#endif

#ifndef IS_NOT_X64
module Hacl_Chacha20Poly1305_256 = Hacl_Chacha20Poly1305_256_bindings.Bindings(Hacl_Chacha20Poly1305_256_stubs)
module Hacl_Poly1305_256 = Hacl_Poly1305_256_bindings.Bindings(Hacl_Poly1305_256_stubs)
module Hacl_Blake2b_256 = Hacl_Blake2b_256_bindings.Bindings(Hacl_Blake2b_256_stubs)
module Hacl_Curve25519_64 = Hacl_Curve25519_64_bindings.Bindings(Hacl_Curve25519_64_stubs)
#endif

module RandomBuffer = struct
  let randombytes ~out = Lib_RandomBuffer_System.randombytes (C.ctypes_buf out) (C.size_uint32 out)
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
    let hash_alg = Alg HashDefs.SHA2_224
    let hash = Hacl_Hash.hacl_Hash_SHA2_hash_224
end)

module SHA2_256 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Alg HashDefs.SHA2_256
    let hash = Hacl_Hash.hacl_Hash_SHA2_hash_256
end)

module SHA2_384 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Alg HashDefs.SHA2_384
    let hash = Hacl_Hash.hacl_Hash_SHA2_hash_384
end)

module SHA2_512 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Alg HashDefs.SHA2_512
    let hash = Hacl_Hash.hacl_Hash_SHA2_hash_512
end)

module SHA3_224 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Len 28
    let hash input input_len output = Hacl_SHA3.hacl_SHA3_sha3_224 input_len input output
end)

module SHA3_256 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Len 32
    let hash input input_len output = Hacl_SHA3.hacl_SHA3_sha3_256 input_len input output
end)

module SHA3_384 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Len 48
    let hash input input_len output = Hacl_SHA3.hacl_SHA3_sha3_384 input_len input output
end)

module SHA3_512 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Len 64
    let hash input input_len output = Hacl_SHA3.hacl_SHA3_sha3_512 input_len input output
end)

module Keccak = struct
  let shake128 ~pt ~digest =
    (* Hacl.SHA3.shake128_hacl *)
    assert (C.disjoint pt digest);
    Hacl_SHA3.hacl_SHA3_shake128_hacl (C.size_uint32 pt) (C.ctypes_buf pt) (C.size_uint32 digest) (C.ctypes_buf digest)
  let shake256 ~pt ~digest =
    (* Hacl.SHA3.shake256_hacl *)
    assert (C.disjoint pt digest);
    Hacl_SHA3.hacl_SHA3_shake256_hacl (C.size_uint32 pt) (C.ctypes_buf pt) (C.size_uint32 digest) (C.ctypes_buf digest)
  let keccak ~rate ~capacity ~suffix ~pt ~digest =
    (* Hacl.Impl.SHA3.keccak *)
    assert (rate mod 8 = 0 && rate / 8 > 0 && rate <= 1600);
    assert (capacity + rate = 1600);
    assert (C.disjoint pt digest);
    Hacl_SHA3.hacl_Impl_SHA3_keccak (UInt32.of_int rate) (UInt32.of_int capacity) (C.size_uint32 pt) (C.ctypes_buf pt) (UInt8.of_int suffix) (C.size_uint32 digest) (C.ctypes_buf digest)

end

module SHA1 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Alg HashDefs.(Legacy SHA1)
    let hash = Hacl_Hash.hacl_Hash_SHA1_legacy_hash
end) [@@deprecated]

module MD5 : HashFunction =
  Make_HashFunction (struct
    let hash_alg = Alg HashDefs.(Legacy MD5)
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

module NaCl = struct
  open Hacl_NaCl

  let get_result r =
    if r = UInt32.zero then
      true
    else
    if r = UInt32.max_int then
      false
    else
      failwith "Unknown return value"
  let check_key_sizes pk sk =
    assert (C.size pk = 32);
    assert (C.size sk = 32)
  let check_easy pt ct n =
    assert (C.size ct = C.size pt + 16);
    assert (C.size n = 24);
    assert (C.disjoint pt ct);
    assert (C.disjoint n pt);
    assert (C.disjoint n ct)
  let check_detached pt ct tag n =
    assert (C.size ct = C.size pt);
    assert (C.size tag = 16);
    assert (C.size n = 24);
    assert (C.disjoint tag ct);
    assert (C.disjoint tag pt);
    assert (C.disjoint n pt);
    assert (C.disjoint n ct)

  let box_beforenm ~pk ~sk ~ck =
    check_key_sizes pk sk;
    assert (C.size ck = 32);
    assert (C.disjoint ck pk);
    assert (C.disjoint ck sk);
    get_result @@ hacl_NaCl_crypto_box_beforenm (C.ctypes_buf ck) (C.ctypes_buf pk) (C.ctypes_buf sk)
  module Easy = struct
    let box ~pt ~n ~pk ~sk ~ct =
      check_key_sizes pk sk;
      check_easy pt ct n;
      get_result @@ hacl_NaCl_crypto_box_easy (C.ctypes_buf ct) (C.ctypes_buf pt) (C.size_uint32 pt) (C.ctypes_buf n) (C.ctypes_buf pk) (C.ctypes_buf sk)
    let box_open ~ct ~n ~pk ~sk ~pt =
      check_key_sizes pk sk;
      check_easy pt ct n;
      get_result @@ hacl_NaCl_crypto_box_open_easy (C.ctypes_buf pt) (C.ctypes_buf ct) (C.size_uint32 ct) (C.ctypes_buf n) (C.ctypes_buf pk) (C.ctypes_buf sk)
    let box_afternm ~pt ~n ~ck ~ct =
      assert (C.size ck = 32);
      check_easy pt ct n;
      get_result @@ hacl_NaCl_crypto_box_easy_afternm (C.ctypes_buf ct) (C.ctypes_buf pt) (C.size_uint32 pt) (C.ctypes_buf n) (C.ctypes_buf ck)
    let box_open_afternm ~ct ~n ~ck ~pt =
      assert (C.size ck = 32);
      check_easy pt ct n;
      get_result @@ hacl_NaCl_crypto_box_open_easy_afternm (C.ctypes_buf pt) (C.ctypes_buf ct) (C.size_uint32 ct) (C.ctypes_buf n) (C.ctypes_buf ck)
    let secretbox ~pt ~n ~key ~ct =
      assert (C.size key = 32);
      check_easy pt ct n;
      get_result @@ hacl_NaCl_crypto_secretbox_easy (C.ctypes_buf ct) (C.ctypes_buf pt) (C.size_uint32 pt) (C.ctypes_buf n) (C.ctypes_buf key)
    let secretbox_open ~ct ~n ~key ~pt=
      assert (C.size key = 32);
      check_easy pt ct n;
      get_result @@ hacl_NaCl_crypto_secretbox_open_easy (C.ctypes_buf pt) (C.ctypes_buf ct) (C.size_uint32 ct) (C.ctypes_buf n) (C.ctypes_buf key)
  end
  module Detached = struct
    let box ~pt ~n ~pk ~sk ~ct ~tag =
      check_key_sizes pk sk;
      check_detached pt ct tag n;
      get_result @@ hacl_NaCl_crypto_box_detached (C.ctypes_buf ct) (C.ctypes_buf tag) (C.ctypes_buf pt) (C.size_uint32 pt) (C.ctypes_buf n) (C.ctypes_buf pk) (C.ctypes_buf sk)
    let box_open ~ct ~tag ~n ~pk ~sk ~pt =
      check_key_sizes pk sk;
      check_detached pt ct tag n;
      get_result @@ hacl_NaCl_crypto_box_open_detached (C.ctypes_buf pt) (C.ctypes_buf ct) (C.ctypes_buf tag) (C.size_uint32 ct) (C.ctypes_buf n) (C.ctypes_buf pk) (C.ctypes_buf sk)
    let box_afternm ~pt ~n ~ck ~ct ~tag =
      assert (C.size ck = 32);
      check_detached pt ct tag n;
      get_result @@ hacl_NaCl_crypto_box_detached_afternm (C.ctypes_buf ct) (C.ctypes_buf tag) (C.ctypes_buf pt) (C.size_uint32 pt) (C.ctypes_buf n) (C.ctypes_buf ck)
    let box_open_afternm ~ct ~tag ~n ~ck ~pt =
      assert (C.size ck = 32);
      check_detached pt ct tag n;
      get_result @@ hacl_NaCl_crypto_box_open_detached_afternm (C.ctypes_buf pt) (C.ctypes_buf ct) (C.ctypes_buf tag) (C.size_uint32 ct) (C.ctypes_buf n) (C.ctypes_buf ck)
    let secretbox ~pt ~n ~key ~ct ~tag =
      assert (C.size key = 32);
      check_detached pt ct tag n;
      get_result @@ hacl_NaCl_crypto_secretbox_detached (C.ctypes_buf ct) (C.ctypes_buf tag) (C.ctypes_buf pt) (C.size_uint32 pt) (C.ctypes_buf n) (C.ctypes_buf key)
    let secretbox_open ~ct ~tag ~n ~key ~pt =
      assert (C.size key = 32);
      check_detached pt ct tag n;
      get_result @@ hacl_NaCl_crypto_secretbox_open_detached (C.ctypes_buf pt) (C.ctypes_buf ct) (C.ctypes_buf tag) (C.size_uint32 ct) (C.ctypes_buf n) (C.ctypes_buf key)
  end
end

module P256 = struct
  let raw_to_compressed ~p ~result =
    (* Hacl.P256.compression_compressed_form *)
    assert (C.size p = 64);
    assert (C.size result = 33);
    Hacl_P256.hacl_P256_compression_compressed_form (C.ctypes_buf p) (C.ctypes_buf result)
  let raw_to_uncompressed ~p ~result =
    (* Hacl.P256.compression_not_compressed_form *)
    assert (C.size p = 64);
    assert (C.size result = 65);
    Hacl_P256.hacl_P256_compression_not_compressed_form (C.ctypes_buf p) (C.ctypes_buf result)
  let compressed_to_raw ~p ~result =
    (* Hacl.P256.decompression_compressed_form *)
    assert (C.size p = 33);
    assert (C.size result = 64);
    Hacl_P256.hacl_P256_decompression_compressed_form (C.ctypes_buf p) (C.ctypes_buf result)
  let uncompressed_to_raw ~p ~result =
    (* Hacl.P256.decompression_not_compressed_form *)
    assert (C.size p = 65);
    assert (C.size result = 64);
    Hacl_P256.hacl_P256_decompression_not_compressed_form (C.ctypes_buf p) (C.ctypes_buf result)
  let dh_initiator ~sk ~pk =
    (* Hacl.P256.ecp256dh_i *)
    assert (C.size pk = 64);
    assert (C.size sk = 32);
    assert (C.disjoint pk sk);
    Hacl_P256.hacl_P256_ecp256dh_i (C.ctypes_buf pk) (C.ctypes_buf sk)
  let dh_responder ~sk ~pk ~shared =
    (* Hacl.P256.ecp256dh_r *)
    assert (C.size shared = 64);
    assert (C.size pk = 64);
    assert (C.size sk = 32);
    assert (C.disjoint shared sk);
    assert (C.disjoint shared pk);
    Hacl_P256.hacl_P256_ecp256dh_r (C.ctypes_buf shared) (C.ctypes_buf pk) (C.ctypes_buf sk)
  let valid_sk ~sk =
    (* Hacl.P256.is_more_than_zero_less_than_order *)
    assert (C.size sk = 32);
    Hacl_P256.hacl_P256_is_more_than_zero_less_than_order (C.ctypes_buf sk)
  let valid_pk ~pk =
    (* Hacl.P256.verify_q *)
    assert (C.size pk = 64);
    Hacl_P256.hacl_P256_verify_q (C.ctypes_buf pk)
  module NoHash = Make_ECDSA (struct
      let min_msg_size = 32
      let sign = Hacl_P256.hacl_P256_ecdsa_sign_p256_without_hash
      let verify = Hacl_P256.hacl_P256_ecdsa_verif_without_hash
    end)
  include NoHash
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

#if not (defined IS_NOT_X64) || defined IS_ARM_8
module Chacha20_Poly1305_128 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let reqs = [AVX]
    let encrypt = Hacl_Chacha20Poly1305_128.hacl_Chacha20Poly1305_128_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_128.hacl_Chacha20Poly1305_128_aead_decrypt
  end)

module Poly1305_128 : MAC =
  Make_Poly1305 (struct
    let reqs = [AVX]
    let mac = Hacl_Poly1305_128.hacl_Poly1305_128_poly1305_mac
end)

module Blake2s_128 : Blake2 =
  Make_Blake2s (struct
    let reqs = [AVX]
    let blake2s = Hacl_Blake2s_128.hacl_Blake2s_128_blake2s
  end)
#else
module Chacha20_Poly1305_128 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let reqs = [AVX]
    let encrypt _ _ _ _ _ _ = failwith "Not implemented on this platform"
    let decrypt _ _ _ _ _ _ = failwith "Not implemented on this platform"
  end)

module Poly1305_128 : MAC =
  Make_Poly1305 (struct
    let reqs = [AVX]
    let mac _ _ _ = failwith "Not implemented on this platform"
end)

module Blake2s_128 : Blake2 =
  Make_Blake2s (struct
    let reqs = [AVX]
    let blake2s _ _ _ = failwith "Not implemented on this platform"
  end)
#endif

#ifndef IS_NOT_X64
module Chacha20_Poly1305_256 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let reqs = [AVX2]
    let encrypt = Hacl_Chacha20Poly1305_256.hacl_Chacha20Poly1305_256_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_256.hacl_Chacha20Poly1305_256_aead_decrypt
  end)

module Poly1305_256 : MAC =
  Make_Poly1305 (struct
      let reqs = [AVX2]
    let mac = Hacl_Poly1305_256.hacl_Poly1305_256_poly1305_mac
end)

module Blake2b_256 : Blake2 =
  Make_Blake2b (struct
    let reqs = [AVX2]
    let blake2b = Hacl_Blake2b_256.hacl_Blake2b_256_blake2b
  end)

module Curve25519_64 : Curve25519 =
  Make_Curve25519 (struct
    let reqs = [BMI2; ADX]
    let secret_to_public = Hacl_Curve25519_64.hacl_Curve25519_64_secret_to_public
    let scalarmult = Hacl_Curve25519_64.hacl_Curve25519_64_scalarmult
    let ecdh = Hacl_Curve25519_64.hacl_Curve25519_64_ecdh
  end)
#else
module Chacha20_Poly1305_256 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
     let reqs = [AVX2]
    let encrypt _ _ _ _ _ _ = failwith "Not implemented on this platform"
    let decrypt _ _ _ _ _ _ = failwith "Not implemented on this platform"
  end)

module Poly1305_256 : MAC =
  Make_Poly1305 (struct
      let reqs = [AVX2]
    let mac _ _ _ = failwith "Not implemented on this platform"
end)

module Blake2b_256 : Blake2 =
  Make_Blake2b (struct
    let reqs = [AVX2]
    let blake2b _ _ _ = failwith "Not implemented on this platform"
  end)

module Curve25519_64 : Curve25519 =
  Make_Curve25519 (struct
    let reqs = [BMI2; ADX]
    let secret_to_public _ _ = failwith "Not implemented on this platform"
    let scalarmult _ _ _ = failwith "Not implemented on this platform"
    let ecdh _ _ _ = failwith "Not implemented on this platform"
  end)
#endif

