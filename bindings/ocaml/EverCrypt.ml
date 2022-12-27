open Ctypes
open Unsigned

open SharedDefs
open SharedFunctors
module C = CBytes

type bytes = CBytes.t

module Hacl_Spec = Hacl_Spec_bindings.Bindings(Hacl_Spec_stubs)

module EverCrypt_AEAD = EverCrypt_AEAD_bindings.Bindings(EverCrypt_AEAD_stubs)
module EverCrypt_Chacha20Poly1305 = EverCrypt_Chacha20Poly1305_bindings.Bindings(EverCrypt_Chacha20Poly1305_stubs)
module EverCrypt_Curve25519 = EverCrypt_Curve25519_bindings.Bindings(EverCrypt_Curve25519_stubs)
module EverCrypt_Hash = EverCrypt_Hash_bindings.Bindings(EverCrypt_Hash_stubs)
module EverCrypt_HMAC = EverCrypt_HMAC_bindings.Bindings(EverCrypt_HMAC_stubs)
module EverCrypt_Poly1305 = EverCrypt_Poly1305_bindings.Bindings(EverCrypt_Poly1305_stubs)
module EverCrypt_HKDF = EverCrypt_HKDF_bindings.Bindings(EverCrypt_HKDF_stubs)
module EverCrypt_DRBG = EverCrypt_DRBG_bindings.Bindings(EverCrypt_DRBG_stubs)
module EverCrypt_Ed25519 = EverCrypt_Ed25519_bindings.Bindings(EverCrypt_Ed25519_stubs)


module Error = struct
  type error_code =
    | UnsupportedAlgorithm
    | InvalidKey
    | AuthenticationFailure
    | InvalidIVLength
    | DecodeError
    | MaximumLengthExceeded
  type 'a result =
    | Success of 'a
    | Error of error_code
  let error n =
    let err = match n with
      | 1 -> UnsupportedAlgorithm
      | 2 -> InvalidKey
      | 3 -> AuthenticationFailure
      | 4 -> InvalidIVLength
      | 5 -> DecodeError
      | 6 -> MaximumLengthExceeded
      | _ -> failwith "Impossible"
    in
    Error err
  let get_result r = match UInt8.to_int r with
    | 0 -> Success ()
    | n -> error n
end

let at_exit_full_major = lazy (at_exit Gc.full_major)

module AEAD = struct
  open Error
  open SharedDefs.AEADDefs
  open EverCrypt_AEAD

  type t = alg * (everCrypt_AEAD_state_s ptr) ptr

  let init ~alg ~key : t result =
    Lazy.force at_exit_full_major;
    assert (C.size key = key_length alg);
    let st = allocate
        ~finalise:(fun st -> everCrypt_AEAD_free (!@ st))
        (ptr everCrypt_AEAD_state_s)
        (from_voidp everCrypt_AEAD_state_s null)
    in
    match UInt8.to_int (everCrypt_AEAD_create_in (alg_definition alg) st (C.ctypes_buf key)) with
    | 0 -> Success (alg, st)
    | n -> error n

  module Noalloc = struct
    let encrypt ~st:(alg, st) ~iv ~ad ~pt ~ct ~tag : unit result =
      (* providers/EverCrypt.AEAD.encrypt_pre *)
      check_sizes ~alg ~iv_len:(C.size iv) ~tag_len:(C.size tag)
        ~ad_len:(C.size ad)~pt_len:(C.size pt) ~ct_len:(C.size ct);
      assert (C.disjoint ct tag);
      assert (C.disjoint iv ct);
      assert (C.disjoint iv tag);
      assert (C.disjoint pt tag);
      assert (C.disjoint pt ad);
      assert (C.disjoint ad ct);
      assert (C.disjoint ad tag);
      get_result (everCrypt_AEAD_encrypt (!@st)
                    (C.ctypes_buf iv) (C.size_uint32 iv) (C.ctypes_buf ad) (C.size_uint32 ad)
                    (C.ctypes_buf pt) (C.size_uint32 pt) (C.ctypes_buf ct) (C.ctypes_buf tag))
    let decrypt ~st:(alg, st) ~iv ~ad ~ct ~tag ~pt : unit result =
      (* EverCrypt.AEAD.decrypt_st *)
      check_sizes ~alg ~iv_len:(C.size iv) ~tag_len:(C.size tag)
        ~ad_len:(C.size ad)~pt_len:(C.size pt) ~ct_len:(C.size ct);
      assert (C.disjoint tag pt);
      assert (C.disjoint tag ct);
      assert (C.disjoint tag ad);
      assert (C.disjoint ct ad);
      assert (C.disjoint pt ad);
      get_result (everCrypt_AEAD_decrypt (!@st)
                    (C.ctypes_buf iv) (C.size_uint32 iv) (C.ctypes_buf ad) (C.size_uint32 ad)
                    (C.ctypes_buf ct) (C.size_uint32 ct) (C.ctypes_buf tag) (C.ctypes_buf pt))
  end
  let encrypt ~st:(alg, st) ~iv ~ad ~pt =
    let ct = C.make (C.size pt) in
    let tag = C.make (tag_length alg) in
    match Noalloc.encrypt ~st:(alg, st) ~iv ~ad ~pt ~ct ~tag with
    | Success () -> Success (ct, tag)
    | Error n -> Error n
  let decrypt ~st:(alg, st) ~iv ~ad ~ct ~tag =
    let pt = C.make (C.size ct) in
    match Noalloc.decrypt ~st:(alg, st) ~iv ~ad ~ct ~tag ~pt with
    | Success () -> Success pt
    | Error n -> Error n
end

module Chacha20_Poly1305 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    (* EverCrypt already performs these runtime checks so all `reqs` attributes in
     * this file are empty since there is no need to do them here. *)
    let reqs = []
    let encrypt = EverCrypt_Chacha20Poly1305.everCrypt_Chacha20Poly1305_aead_encrypt
    let decrypt = EverCrypt_Chacha20Poly1305.everCrypt_Chacha20Poly1305_aead_decrypt
  end)

module Curve25519 : Curve25519 =
  Make_Curve25519 (struct
    let reqs = []
    let secret_to_public = EverCrypt_Curve25519.everCrypt_Curve25519_secret_to_public
    let scalarmult = EverCrypt_Curve25519.everCrypt_Curve25519_scalarmult
    let ecdh = EverCrypt_Curve25519.everCrypt_Curve25519_ecdh
  end)

module Ed25519 : EdDSA =
  Make_EdDSA (struct
  let secret_to_public = EverCrypt_Ed25519.everCrypt_Ed25519_secret_to_public
  let sign = EverCrypt_Ed25519.everCrypt_Ed25519_sign
  let verify = EverCrypt_Ed25519.everCrypt_Ed25519_verify
  let expand_keys = EverCrypt_Ed25519.everCrypt_Ed25519_expand_keys
  let sign_expanded = EverCrypt_Ed25519.everCrypt_Ed25519_sign_expanded
  end)

module Hash = struct
  open HashDefs
  open EverCrypt_Hash
  module Noalloc = struct
    let hash ~alg ~msg ~digest =
      check_max_buffer_len (C.size msg);
      assert (C.size digest = digest_len alg);
      assert (C.disjoint digest msg);
      everCrypt_Hash_Incremental_hash (alg_definition alg) (C.ctypes_buf digest) (C.ctypes_buf msg) (C.size_uint32 msg)
    let finish ~st:(alg, t) ~digest =
      assert (C.size digest = digest_len alg);
      everCrypt_Hash_Incremental_finish t (C.ctypes_buf digest)
  end
  (* TODO: get rid of the `alg` here by using `alg_of_state` *)
  type t = alg * everCrypt_Hash_Incremental_hash_state Ctypes_static.ptr
  let init ~alg =
    Lazy.force at_exit_full_major;
    let alg_spec = alg_definition alg in
    let st = everCrypt_Hash_Incremental_create_in alg_spec in
    everCrypt_Hash_Incremental_init st;
    Gc.finalise everCrypt_Hash_Incremental_free st;
    alg, st
  let update ~st:(_alg, t) ~msg =
    check_max_buffer_len (C.size msg);
    let e = everCrypt_Hash_Incremental_update t (C.ctypes_buf msg) (C.size_uint32 msg) in
    (* can return `MaximumLengthExceeded` if total length exceeds limit, as defined
     * in Spec.Hash.Definitions.max_input_length *)
    assert (Error.get_result e = Error.Success ())
  let finish ~st:(alg, t) =
    let digest = C.make (digest_len alg) in
    Noalloc.finish ~st:(alg, t) ~digest;
    digest
  let hash ~alg ~msg =
    let digest = C.make (digest_len alg) in
    Noalloc.hash ~alg ~msg ~digest;
    digest
end

module HMAC = struct
  open EverCrypt_HMAC
  let is_supported_alg ~alg =
    everCrypt_HMAC_is_supported_alg (HashDefs.alg_definition alg)
  module Noalloc = struct
    let mac ~alg ~key ~msg ~tag=
      (* Hacl.HMAC.compute_st *)
      assert (C.size tag = HashDefs.digest_len alg);
      assert (C.disjoint msg tag);
      check_max_buffer_len (C.size key);
      check_max_buffer_len (C.size msg);
      everCrypt_HMAC_compute (HashDefs.alg_definition alg) (C.ctypes_buf tag) (C.ctypes_buf key) (C.size_uint32 key) (C.ctypes_buf msg) (C.size_uint32 msg)
  end
  let mac ~alg ~key ~msg =
    let tag = C.make (HashDefs.digest_len alg) in
    Noalloc.mac ~alg ~key ~msg ~tag;
    tag
end

module Poly1305 : MAC =
  Make_Poly1305 (struct
    let reqs = []
    let mac dst data_len data key = EverCrypt_Poly1305.everCrypt_Poly1305_poly1305 dst data data_len key
end)

module HKDF = struct
  open EverCrypt_HKDF
  module Noalloc = struct
    let extract ~alg ~salt ~ikm ~prk =
      (* Hacl.HKDF.extract_st *)
      assert (C.size prk = HashDefs.digest_len alg);
      assert (C.disjoint salt prk);
      assert (C.disjoint ikm prk);
      check_max_buffer_len (C.size salt);
      check_max_buffer_len (C.size ikm);
      everCrypt_HKDF_extract (HashDefs.alg_definition alg) (C.ctypes_buf prk) (C.ctypes_buf salt) (C.size_uint32 salt) (C.ctypes_buf ikm) (C.size_uint32 ikm)
    let expand ~alg ~prk ~info ~okm =
      (* Hacl.HKDF.expand_st *)
      assert (C.size okm <= 255 * HashDefs.digest_len alg);
      assert (C.disjoint okm prk);
      assert (HashDefs.digest_len alg <= C.size prk);
      check_max_buffer_len (C.size info);
      check_max_buffer_len (C.size prk);
      everCrypt_HKDF_expand (HashDefs.alg_definition alg) (C.ctypes_buf okm) (C.ctypes_buf prk) (C.size_uint32 prk) (C.ctypes_buf info) (C.size_uint32 info) (C.size_uint32 okm)
  end
  let extract ~alg ~salt ~ikm =
    let prk = C.make (HashDefs.digest_len alg) in
    Noalloc.extract ~alg ~salt ~ikm ~prk;
    prk
  let expand ~alg ~prk ~info ~size =
    let okm = C.make size in
    Noalloc.expand ~alg ~prk ~info ~okm;
    okm
end

module DRBG = struct
  open EverCrypt_DRBG
  type t = everCrypt_DRBG_state_s ptr
  module Noalloc = struct
    let generate ?(additional_input=Bytes.empty) st output =
      (* EverCrypt.DRBG.generate_st *)
      assert (C.disjoint output additional_input);
      everCrypt_DRBG_generate (C.ctypes_buf output) st (C.size_uint32 output) (C.ctypes_buf additional_input) (C.size_uint32 additional_input)
  end
  let is_supported_alg alg =
    (* as defined in Spec.HMAC_DRBG, excluding SHA-1 *)
    alg = HashDefs.SHA2_256 || alg = HashDefs.SHA2_384 || alg = HashDefs.SHA2_512
  let instantiate ?(personalization_string=Bytes.empty) alg =
    (* EverCrypt.DRBG.instantiate_st *)
    if is_supported_alg alg then
      let st = everCrypt_DRBG_create (HashDefs.alg_definition alg) in
      if everCrypt_DRBG_instantiate st (C.ctypes_buf personalization_string) (C.size_uint32 personalization_string) then begin
        Gc.finalise everCrypt_DRBG_uninstantiate st;
        Some st
      end else
        None
    else
      None
  let generate ?(additional_input=Bytes.empty) st size =
    let output = C.make size in
    if Noalloc.generate ~additional_input st output then
      Some output
    else
      None
  let reseed ?(additional_input=Bytes.empty) st =
    (* EverCrypt.DRBG.reseed_st *)
    everCrypt_DRBG_reseed st (C.ctypes_buf additional_input) (C.size_uint32 additional_input)
end
