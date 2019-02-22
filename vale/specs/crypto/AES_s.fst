module AES_s

// IMPORTANT: This specification is written assuming a little-endian mapping from bytes to quad32s
//            This is explicit in key_schedule_to_round_keys when we construct the round_key rk,
//            but it also applies implicitly to the input quad32

open Prop_s
open Opaque_s
open Words_s
open Words.Four_s
open Words.Seq_s
open Types_s
open FStar.Seq
open FStar.Mul

// substitution is endian-neutral;
// others operations assume that the quad32 and nat32 values are little-endian interpretations
// of 16-byte and 4-byte sequences
assume val mix_columns_LE (q:quad32) : quad32
assume val inv_mix_columns_LE (q:quad32) : quad32
assume val sub_bytes (q:quad32) : quad32
assume val inv_sub_bytes (q:quad32) : quad32
assume val shift_rows_LE (q:quad32) : quad32
assume val inv_shift_rows_LE (q:quad32) : quad32
assume val rot_word_LE (w:nat32) : nat32
assume val sub_word (w:nat32) : nat32

assume val commute_sub_bytes_shift_rows (q:quad32) : Lemma
  (sub_bytes (shift_rows_LE q) == shift_rows_LE (sub_bytes q))

assume val commute_rot_word_sub_word (x:nat32) : Lemma
  (rot_word_LE (sub_word x) == sub_word (rot_word_LE x))

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

let is_aes_key_LE (alg:algorithm) (s:seq nat32) : prop0 = length s == nk alg
type aes_key_LE (alg:algorithm) : eqtype = s:(seq nat32){is_aes_key_LE alg s}
let is_aes_key (alg:algorithm) (s:seq nat8) : prop0 = length s == 4 * nk alg
type aes_key (alg:algorithm) : eqtype = s:(seq nat8){is_aes_key alg s}

let round (state round_key:quad32) =
  let s = sub_bytes state in
  let s = shift_rows_LE s in
  let s = mix_columns_LE s in
  let s = quad32_xor s round_key in
  s

let rec rounds (init:quad32) (round_keys:seq quad32) (n:nat{n < length round_keys}) : quad32 =
  if n = 0 then
    init
  else
    round (rounds init round_keys (n - 1)) (index round_keys n)

let cipher (alg:algorithm) (input:quad32) (round_keys:seq quad32) : Pure quad32
  (requires length round_keys == nr alg + 1)
  (ensures fun _ -> True)
  =
  let state = quad32_xor input (index round_keys 0) in
  let state = rounds state round_keys (nr alg - 1) in
  let state = sub_bytes state in
  let state = shift_rows_LE state in
  let state = quad32_xor state (index round_keys (nr alg)) in
  state

let rec expand_key_def (alg:algorithm) (key:aes_key_LE alg) (size:nat{size <= (nb * ((nr alg) + 1))})
  : (ek_LE:seq nat32 {length ek_LE == size}) =
  if size = 0 then empty
  else
    let w = expand_key_def alg key (size - 1) in
    let i = size - 1 in
    if 0 <= i && i < nk alg then
      append w (create 1 (index key i))
    else
      let temp =
        if i % (nk alg) = 0 then
          nat32_xor (sub_word (rot_word_LE (index w (i-1)))) (aes_rcon ((i / (nk alg)) - 1))
        else if nk alg > 6 && i % (nk alg) = 4 then
          sub_word (index w (i - 1))
        else
          index w (i - 1)
        in
      append w (create 1 (nat32_xor (index w (i - (nk alg))) temp))

let expand_key = make_opaque expand_key_def

let rec key_schedule_to_round_keys (rounds:nat) (w:seq nat32 {length w >= 4 * rounds})
  : (round_keys:seq quad32 {length round_keys == rounds}) =
  if rounds = 0 then empty
  else
    let round_keys = key_schedule_to_round_keys (rounds - 1) w in
    let rk = Mkfour (index w (4 * rounds - 4)) (index w (4 * rounds - 3)) (index w (4 * rounds - 2)) (index w (4 * rounds - 1)) in
    append round_keys (create 1 rk)

let key_to_round_keys_LE_def (alg:algorithm) (key:seq nat32) : Pure (seq quad32)
  (requires is_aes_key_LE alg key)
  (ensures fun round_keys -> length round_keys == nr alg + 1)
  =
  key_schedule_to_round_keys (nr alg + 1) (expand_key alg key (nb * (nr alg + 1)))

let key_to_round_keys_LE = make_opaque key_to_round_keys_LE_def

let aes_encrypt_LE_def (alg:algorithm) (key:seq nat32) (input_LE:quad32) : Pure quad32
  (requires is_aes_key_LE alg key)
  (ensures fun _ -> True)
  =
  cipher alg input_LE (key_to_round_keys_LE alg key)

//let aes_encrypt_LE = make_opaque aes_encrypt_LE_def
unfold let aes_encrypt_LE = aes_encrypt_LE_def

#push-options "--z3rlimit 20"
let key_to_round_keys (alg:algorithm) (key:aes_key alg)
  : (round_keys:seq nat8 {length round_keys == 16 * (nr alg + 1)}) =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  le_seq_quad32_to_bytes (key_to_round_keys_LE alg key_LE)
#pop-options

let aes_encrypt (alg:algorithm) (key:aes_key alg) (input:seq16 nat8) : seq16 nat8 =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let input_LE = le_bytes_to_quad32 input in
  le_quad32_to_bytes (aes_encrypt_LE alg key_LE input_LE)
