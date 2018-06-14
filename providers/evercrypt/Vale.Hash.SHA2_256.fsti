(** Stripped down version of module in secure_api/vale/asm that extracts to a .h;
 *  The hand-written C implementation is in secure_api/vale/asm
 *)
module Vale.Hash.SHA2_256

open EverCrypt.Helpers

val init:
  state: uint32_p ->
  Stack_ unit

val update:
  state: uint32_p ->
  data : uint8_p ->
  Stack_ unit

val update_last:
  state: uint32_p ->
  data : uint8_p  ->
  len  : uint32_t ->
  Stack_ unit

val finish:
  state : uint32_p ->
  hash  : uint8_p ->
  Stack_ unit
