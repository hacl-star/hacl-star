module Vale.AES.AES_common_s

// IMPORTANT: This specification is written assuming a little-endian mapping from bytes to quad32s
//            This is explicit in key_schedule_to_round_keys when we construct the round_key rk,
//            but it also applies implicitly to the input quad32

open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq_s
open Vale.Def.Types_s
open FStar.Seq
open FStar.Mul

// substitution is endian-neutral;
assume val sub_bytes (q:quad32) : quad32
assume val inv_sub_bytes (q:quad32) : quad32
assume val sub_word (w:nat32) : nat32

type algorithm:eqtype = | AES_128 | AES_192 | AES_256

let aes_rcon (i:int) : nat32 =
  if i = 0 then 0x01 else
  if i = 1 then 0x02 else
  if i = 2 then 0x04 else
  if i = 3 then 0x08 else
  if i = 4 then 0x10 else
  if i = 5 then 0x20 else
  if i = 6 then 0x40 else
  if i = 7 then 0x80 else
  if i = 8 then 0x1b else
  0x36

// AES fixes Rijndael's block size at 4 32-bit words
let nb = 4

// Number of key words
unfold let nk(alg:algorithm) =
  match alg with
  | AES_128 -> 4
  | AES_192 -> 6
  | AES_256 -> 8

// Number of rounds
unfold let nr(alg:algorithm) =
  match alg with
  | AES_128 -> 10
  | AES_192 -> 12
  | AES_256 -> 14

let is_aes_key (alg:algorithm) (s:seq nat8) : prop0 = length s == 4 * nk alg
type aes_key (alg:algorithm) : eqtype = s:(seq nat8){is_aes_key alg s}
