open Ctypes
open PosixTypes
open Foreign

(* This module implements EverCrypt.Bytes, using fstarlib's `type bytes =
 * string`. *)

(* See Santiago's comment in PKI.ml *)
let () =
  if Sys.os_type = "Win32" then
    ignore (Dl.dlopen ~filename:"libevercrypt.so" ~flags:[])

let x25519_ =
  foreign "EverCrypt_x25519" (
    string @->
    string @->
    string @->
    returning void)

let x25519 secret base =
  let dst = String.make 32 '\000' in
  x25519_ dst secret base;
  dst
