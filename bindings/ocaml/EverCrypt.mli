(** This module exposes the EverCrypt cryptographic provider, which offers
    agile and multiplexing interfaces for HACL* primitives *)

open SharedDefs

module Error : sig
  type error_code =
    | UnsupportedAlgorithm
    | InvalidKey
    | AuthenticationFailure
    | InvalidIVLength
    | DecodeError
  type 'a result =
    | Success of 'a
    | Error of error_code
end
(** Return type used for {!AEAD} functions *)


(** {1 AEAD}
    Algorithms for AEAD (authenticated encryption with additional data) *)

(** {2 Agile interface } *)

module AEAD : sig
  type t
  type alg =
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305

  val init : alg:alg -> key:CBytes.t -> t Error.result
  (** [init alg key] tries to allocate the internal state for algorithm [alg] with [key]
      and returns a {!t} if successful or an {!Error.error_code} otherwise. *)

  val encrypt : st:t -> iv:CBytes.t -> ad:CBytes.t -> pt:CBytes.t -> ct:CBytes.t -> tag:CBytes.t -> unit Error.result
  (** [encrypt st iv ad pt ct tag] takes a state [st], an initial value [iv], additional data
      [ad], and plaintext [pt], as well as output buffers [ct], which, if successful, will
      contain the encrypted [pt], and [tag], which will contain the authentication tag for
      the plaintext and the associated data. *)

  val decrypt : st:t -> iv:CBytes.t -> ad:CBytes.t -> ct:CBytes.t -> tag:CBytes.t -> pt:CBytes.t -> unit Error.result
  (** [decrypt st iv ad ct tag pt] takes a state [st], the initial value [iv], additional
      data [ad], ciphertext [ct], and authentication tag [tag], as well as output buffer [pt],
      which, if sucessful, will contain the decrypted [ct]. *)

end
(** Agile, multiplexing AEAD interface exposing AES128-GCM, AES256-GCM, and Chacha20-Poly1305

    To use the agile AEAD interface, users first need to initialise an internal state
    using {!init}. This state will then need to be passed to every call to {!encrypt}
    and {!decrypt}. It can be reused as many times as needed. The user is not required
    to manually free the state.

    The [tag] buffer must be 16 bytes long. For [key] and [iv], each algorithm
    has different constraints:
    - AES128-GCM: [key] = 16 bytes , [iv] > 0 bytes
    - AES256-GCM: [key] = 32 bytes, [iv] > 0 bytes
    - Chacha20-Poly1305: [key] = 32 bytes, [iv] = 12 bytes
*)


(** {2 Chacha20-Poly1305} *)

module Chacha20_Poly1305 : Chacha20_Poly1305
(** Multiplexing interface for Chacha20-Poly1305 *)

(** {1 ECDH, ECDSA, and EdDSA } *)
(** {2 Curve25519} *)

module Curve25519 : Curve25519
(** Multiplexing interface for ECDH using Curve25519 *)

(** {2 Ed25519} *)

module Ed25519 : EdDSA


(** {1 Hashing } *)
(** {2 Agile interface } *)

module Hash : sig
  type t
  val init : HashDefs.alg -> t
  val update : t -> CBytes.t -> unit
  val finish : t -> CBytes.t -> unit
  val hash : HashDefs.alg -> CBytes.t -> CBytes.t -> unit
end

(** {2 SHA-2} *)

module SHA2_224 : HashFunction

module SHA2_256 : HashFunction


(** {1 MACs} *)
(** {2 HMAC} *)

module HMAC : sig
  val is_supported_alg : HashDefs.alg -> bool
  val mac : HashDefs.alg -> CBytes.t -> CBytes.t -> CBytes.t -> unit
end

module HMAC_SHA2_256 : MAC

module HMAC_SHA2_384 : MAC

module HMAC_SHA2_512 : MAC

(** {2 Poly1305} *)

module Poly1305 : MAC


(** {1 Key derivation} *)
(** {2 HKDF} *)

module HKDF : sig
  val expand : HashDefs.alg -> CBytes.t -> CBytes.t -> CBytes.t -> unit
  val extract : HashDefs.alg -> CBytes.t -> CBytes.t -> CBytes.t -> unit
end

module HKDF_SHA2_256 : HKDF

module HKDF_SHA2_384 : HKDF

module HKDF_SHA2_512 : HKDF

(** {1 DRBG} *)

module DRBG : sig
  type t
  val instantiate : ?personalization_string: CBytes.t -> HashDefs.alg -> t option
  val reseed : ?additional_input: CBytes.t -> t -> bool
  val generate : ?additional_input: CBytes.t -> t -> CBytes.t -> bool
  val uninstantiate : t -> unit
end
