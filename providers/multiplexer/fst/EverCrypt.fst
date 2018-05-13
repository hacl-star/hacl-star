module EverCrypt

module Hacl = EverCrypt.Hacl
module Vale = EverCrypt.Vale

open EverCrypt.Native
open EverCrypt.Helpers
open C.Failure

/// Some remarks here.
///
/// - Eta-expanding helps avoid KreMLin errors down the line (and is more
///   efficient in C.)
/// - The match is complete, it'd be too complicated to encode refinements for
///   sha256_impl, etc.
let sha256_init state =
  match sha256_impl with
  | Hacl -> Hacl.sha256_init state
  | Vale -> Vale.sha256_init state
  | OpenSSL -> failwith !$"TODO: sha256_init/OpenSSL"

let sha256_update state data =
  match sha256_impl with
  | Hacl -> Hacl.sha256_update state data
  | Vale -> Vale.sha256_update state data
  | OpenSSL -> failwith !$"TODO: sha256_update/OpenSSL"

let sha256_update_multi state data n =
  match sha256_impl with
  | Hacl -> Hacl.sha256_update_multi state data n
  | Vale -> Vale.sha256_update_multi state data n
  | OpenSSL -> failwith !$"TODO: sha256_update_multi/OpenSSL"

let sha256_update_last state data n =
  match sha256_impl with
  | Hacl -> Hacl.sha256_update_last state data n
  | Vale -> Vale.sha256_update_last state data n
  | OpenSSL -> failwith !$"TODO: sha256_update/OpenSSL"

let sha256_finish state data =
  match sha256_impl with
  | Hacl -> Hacl.sha256_finish state data
  | Vale -> Vale.sha256_finish state data
  | OpenSSL -> failwith !$"TODO: sha256_finish/OpenSSL"

let sha256_hash dst src len =
  match sha256_impl with
  | Hacl -> Hacl.sha256_hash dst src len
  | Vale -> failwith !$"TODO: sha256_hash/Vale"
  | OpenSSL -> failwith !$"TODO: sha256_hash/OpenSSL"

let sha384_init state =
  match sha384_impl with
  | Hacl -> Hacl.sha384_init state
  | Vale -> failwith !$"TODO: sha384_init/Vale"
  | OpenSSL -> failwith !$"TODO: sha384_init/OpenSSL"

let sha384_update state data =
  match sha384_impl with
  | Hacl -> Hacl.sha384_update state data
  | Vale -> failwith !$"TODO: sha384_update/Vale"
  | OpenSSL -> failwith !$"TODO: sha384_update/OpenSSL"

let sha384_update_multi state data n =
  match sha384_impl with
  | Hacl -> Hacl.sha384_update_multi state data n
  | Vale -> failwith !$"TODO: sha384_update_multi/Vale"
  | OpenSSL -> failwith !$"TODO: sha384_update_multi/OpenSSL"

let sha384_update_last state data n =
  match sha384_impl with
  | Hacl -> Hacl.sha384_update_last state data n
  | Vale -> failwith !$"TODO: sha384_update/Vale"
  | OpenSSL -> failwith !$"TODO: sha384_update/OpenSSL"

let sha384_finish state data =
  match sha384_impl with
  | Hacl -> Hacl.sha384_finish state data
  | Vale -> failwith !$"TODO: sha384_finish/Vale"
  | OpenSSL -> failwith !$"TODO: sha384_finish/OpenSSL"

let sha384_hash dst src len =
  match sha384_impl with
  | Hacl -> Hacl.sha384_hash dst src len
  | Vale -> failwith !$"TODO: sha384_hash/Vale"
  | OpenSSL -> failwith !$"TODO: sha384_hash/OpenSSL"

let sha512_init state =
  match sha512_impl with
  | Hacl -> Hacl.sha512_init state
  | Vale -> failwith !$"TODO: sha512_init/Vale"
  | OpenSSL -> failwith !$"TODO: sha512_init/OpenSSL"

let sha512_update state data =
  match sha512_impl with
  | Hacl -> Hacl.sha512_update state data
  | Vale -> failwith !$"TODO: sha512_update/Vale"
  | OpenSSL -> failwith !$"TODO: sha512_update/OpenSSL"

let sha512_update_multi state data n =
  match sha512_impl with
  | Hacl -> Hacl.sha512_update_multi state data n
  | Vale -> failwith !$"TODO: sha512_update_multi/Vale"
  | OpenSSL -> failwith !$"TODO: sha512_update_multi/OpenSSL"

let sha512_update_last state data n =
  match sha512_impl with
  | Hacl -> Hacl.sha512_update_last state data n
  | Vale -> failwith !$"TODO: sha512_update/Vale"
  | OpenSSL -> failwith !$"TODO: sha512_update/OpenSSL"

let sha512_finish state data =
  match sha512_impl with
  | Hacl -> Hacl.sha512_finish state data
  | Vale -> failwith !$"TODO: sha512_finish/Vale"
  | OpenSSL -> failwith !$"TODO: sha512_finish/OpenSSL"

let sha512_hash dst src len =
  match sha512_impl with
  | Hacl -> Hacl.sha512_hash dst src len
  | Vale -> failwith !$"TODO: sha512_hash/Vale"
  | OpenSSL -> failwith !$"TODO: sha512_hash/OpenSSL"

let x25519 dst secret base =
  match x25519_impl with
  | Hacl -> Hacl.x25519 dst secret base
  | Vale -> failwith !$"TODO: x25519/Vale"
  | OpenSSL -> failwith !$"TODO: x25519/OpenSSL"

let aes256_gcm_encrypt cipher tag key iv plaintext len ad adlen =
  match aes_gcm_impl with
  | Hacl -> failwith !$"TODO: aes-gcm/hacl"
  | Vale -> failwith !$"TODO: aes-gcm/vale"
  | OpenSSL -> EverCrypt.OpenSSL.aes256_gcm_encrypt cipher tag key iv plaintext len ad adlen
