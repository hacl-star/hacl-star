module EverCrypt.HKDF

open Hacl.HKDF

friend EverCrypt.HMAC

/// Four monomorphized variants, for callers who already know which algorithm they want

(** @type: true
*)
val expand_sha1: expand_st SHA1

(** @type: true
*)
val extract_sha1: extract_st SHA1

(** @type: true
*)
val expand_sha2_256: expand_st SHA2_256

(** @type: true
*)
val extract_sha2_256: extract_st SHA2_256

(** @type: true
*)
val expand_sha2_384: expand_st SHA2_384

(** @type: true
*)
val extract_sha2_384: extract_st SHA2_384

(** @type: true
*)
val expand_sha2_512: expand_st SHA2_512

(** @type: true
*)
val extract_sha2_512: extract_st SHA2_512

(** @type: true
*)
val expand_blake2s: expand_st Blake2S

(** @type: true
*)
val extract_blake2s: extract_st Blake2S

(** @type: true
*)
val expand_blake2b: expand_st Blake2B

(** @type: true
*)
val extract_blake2b: extract_st Blake2B

let expand_sha1 =
  mk_expand SHA1 EverCrypt.HMAC.compute_sha1

let extract_sha1 =
  mk_extract SHA1 EverCrypt.HMAC.compute_sha1

let expand_sha2_256 =
  mk_expand SHA2_256 EverCrypt.HMAC.compute_sha2_256

let extract_sha2_256 =
  mk_extract SHA2_256 EverCrypt.HMAC.compute_sha2_256

let expand_sha2_384 =
  mk_expand SHA2_384 EverCrypt.HMAC.compute_sha2_384

let extract_sha2_384 =
  mk_extract SHA2_384 EverCrypt.HMAC.compute_sha2_384

let expand_sha2_512 =
  mk_expand SHA2_512 EverCrypt.HMAC.compute_sha2_512

let extract_sha2_512 =
  mk_extract SHA2_512 EverCrypt.HMAC.compute_sha2_512

let expand_blake2s =
  mk_expand Blake2S EverCrypt.HMAC.compute_blake2s

let extract_blake2s =
  mk_extract Blake2S EverCrypt.HMAC.compute_blake2s

let expand_blake2b =
  mk_expand Blake2B EverCrypt.HMAC.compute_blake2b

let extract_blake2b =
  mk_extract Blake2B EverCrypt.HMAC.compute_blake2b

let expand a okm prk prklen info infolen len =
  match a with
  | SHA1 -> expand_sha1 okm prk prklen info infolen len
  | SHA2_256 -> expand_sha2_256 okm prk prklen info infolen len
  | SHA2_384 -> expand_sha2_384 okm prk prklen info infolen len
  | SHA2_512 -> expand_sha2_512 okm prk prklen info infolen len
  | Blake2S -> expand_blake2s okm prk prklen info infolen len
  | Blake2B -> expand_blake2b okm prk prklen info infolen len

let extract a prk salt saltlen ikm ikmlen =
  match a with
  | SHA1 -> extract_sha1 prk salt saltlen ikm ikmlen
  | SHA2_256 -> extract_sha2_256 prk salt saltlen ikm ikmlen
  | SHA2_384 -> extract_sha2_384 prk salt saltlen ikm ikmlen
  | SHA2_512 -> extract_sha2_512 prk salt saltlen ikm ikmlen
  | Blake2S -> extract_blake2s prk salt saltlen ikm ikmlen
  | Blake2B -> extract_blake2b prk salt saltlen ikm ikmlen
