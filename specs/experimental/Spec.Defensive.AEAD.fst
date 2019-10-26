module Spec.Defensive.AEAD

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 150"

include Spec.Agile.AEAD.Hacl

/// API

val encrypt:
    a: algorithm
  -> k: key a
  -> n: nonce a
  -> m: bytes
  -> aad: bytes ->
  Tot (option bytes)

let encrypt a k n m aad =
  if not (
    length m <= max_size_t
    && length m + size_tag a <= max_size_t
    && length m + padlen a (length m) <= max_size_t
    && length aad <= max_size_t
    && length aad + padlen a (length aad) <= max_size_t
  ) then None
  else Some (Spec.Agile.AEAD.Hacl.encrypt a k n m aad)


val decrypt:
    a: algorithm
  -> k: key a
  -> n: nonce a
  -> ct: bytes
  -> aad: bytes ->
  Tot (option bytes)

let decrypt a k n ct aad =
  if not (
    size_tag a <= length ct
    && length ct <= max_size_t
    && length aad <= max_size_t
    && length aad + padlen a (length aad) <= max_size_t
  ) then None
  else (
    let result: option (lbytes (length ct - size_tag a)) = Spec.Agile.AEAD.Hacl.decrypt a k n ct aad in
    admit(); // FIXME: neet to relax the output type
    result)


val encrypt_detached:
    a: algorithm
  -> k: key a
  -> n: nonce a
  -> m: bytes
  -> aad: bytes ->
  Tot (option (bytes & bytes))

let encrypt_detached a k n m aad =
  if not (
    length m <= max_size_t
    && length m + size_tag a <= max_size_t
    && length m + padlen a (length m) <= max_size_t
    && length aad <= max_size_t
    && length aad + padlen a (length aad) <= max_size_t
  ) then None
  else (
    let output: lbytes (length m) & lbytes (size_tag a) = Spec.Agile.AEAD.Hacl.encrypt_detached a k n m aad in
    admit(); // FIXME: neet to relax the output type
    Some output)


val decrypt_detached:
    a: algorithm
  -> k: key a
  -> n: nonce a
  -> c: bytes
  -> mac: tag a
  -> aad: bytes ->
  Tot (option bytes)

let decrypt_detached a k n c mac aad =
  if not (
    length c <= max_size_t
    && length aad <= max_size_t
    && length aad + padlen a (length aad) <= max_size_t
  ) then None
  else (
    let result:  (option (lbytes (length c))) = Spec.Agile.AEAD.Hacl.decrypt_detached a k n c mac aad in
    admit(); // FIXME: neet to relax the output type
    result)
