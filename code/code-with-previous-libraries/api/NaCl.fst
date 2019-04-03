module NaCl

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open FStar.HyperStack.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast

module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

let crypto_secretbox_detached c mac m mlen n k = Hacl.SecretBox.ZeroPad.crypto_secretbox_detached c mac m mlen n k

let crypto_secretbox_open_detached m c mac clen n k = Hacl.SecretBox.ZeroPad.crypto_secretbox_open_detached m c mac clen n k

let crypto_secretbox_easy c m mlen n k =
    Hacl.SecretBox.ZeroPad.crypto_secretbox_easy c m mlen n k

let crypto_secretbox_open_easy m c clen n k =
    Hacl.SecretBox.ZeroPad.crypto_secretbox_open_easy m c clen n k

let crypto_box_beforenm k pk sk =
  Hacl.Box.ZeroPad.crypto_box_beforenm k pk sk

let crypto_box_detached_afternm c mac m mlen n k =
  Hacl.Box.ZeroPad.crypto_box_detached_afternm c mac m mlen n k

let crypto_box_detached c mac m mlen n pk sk =
  Hacl.Box.ZeroPad.crypto_box_detached c mac m mlen n pk sk

let crypto_box_open_detached m c mac mlen n pk sk =
  Hacl.Box.ZeroPad.crypto_box_open_detached m c mac mlen n pk sk

let crypto_box_easy_afternm c m mlen n k =
  Hacl.Box.ZeroPad.crypto_box_easy_afternm c m mlen n k

let crypto_box_easy c m mlen n pk sk =
  Hacl.Box.ZeroPad.crypto_box_easy c m mlen n pk sk

let crypto_box_open_easy m c mlen n pk sk =
  Hacl.Box.ZeroPad.crypto_box_open_easy m c mlen n pk sk

let crypto_box_open_detached_afternm m c mac mlen n k =
  Hacl.Box.ZeroPad.crypto_box_open_detached_afternm m c mac mlen n k

let crypto_box_open_easy_afternm m c mlen n k =
  Hacl.Box.ZeroPad.crypto_box_open_easy_afternm m c mlen n k
