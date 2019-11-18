module EverCrypt.HKDF

open Hacl.HKDF

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


let expand a okm prk prklen info infolen len = 
  match a with
  | SHA1 -> expand_sha1 okm prk prklen info infolen len
  | SHA2_256 -> expand_sha2_256 okm prk prklen info infolen len
  | SHA2_384 -> expand_sha2_384 okm prk prklen info infolen len
  | SHA2_512 -> expand_sha2_512 okm prk prklen info infolen len

let extract a prk salt saltlen ikm ikmlen = 
  match a with
  | SHA1 -> extract_sha1 prk salt saltlen ikm ikmlen
  | SHA2_256 -> extract_sha2_256 prk salt saltlen ikm ikmlen
  | SHA2_384 -> extract_sha2_384 prk salt saltlen ikm ikmlen
  | SHA2_512 -> extract_sha2_512 prk salt saltlen ikm ikmlen
