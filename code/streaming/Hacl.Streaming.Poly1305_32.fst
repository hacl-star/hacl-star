module Hacl.Streaming.Poly1305_32

open Hacl.Meta.Poly1305
open Hacl.Poly1305_32

friend Hacl.Meta.Poly1305

(* The one-shot MAC *)
[@@ Comment "Compute the Poly1305 MAC of a message.

@param output Pointer to 16 bytes of memory where the MAC is written to.
@param input Pointer to `input_len` bytes of memory where the message is read from.
@param input_len Length of the message.
@param key Pointer to 32 bytes of memory where the key is read from."]
let mac = poly1305_poly1305_mac_higher #M32 True poly1305_finish poly1305_update poly1305_init
