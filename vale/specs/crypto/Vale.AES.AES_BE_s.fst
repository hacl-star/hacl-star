module Vale.AES.AES_BE_s

// IMPORTANT: This specification is written assuming a big-endian mapping from bytes to quad32s
//            This is explicit in key_schedule_to_round_keys when we construct the round_key rk,
//            but it also applies implicitly to the input quad32

open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Seq
open FStar.Mul
include Vale.AES.AES_common_s

// operations assume that the quad32 and nat32 values are big-endian interpretations
// of 16-byte and 4-byte sequences
assume val mix_columns (q:quad32) : quad32
assume val inv_mix_columns (q:quad32) : quad32
assume val shift_rows (q:quad32) : quad32
assume val inv_shift_rows (q:quad32) : quad32
assume val rot_word (w:nat32) : nat32

assume val commute_rot_word_sub_word (x:nat32) (rcon:nat32) : Lemma
  (rot_word (sub_word x *^ ishl32 rcon 16) == sub_word (rot_word x) *^ rcon)

let is_aes_key_word (alg:algorithm) (s:seq nat32) : prop0 = length s == nk alg
type aes_key_word (alg:algorithm) : eqtype = s:(seq nat32){is_aes_key_word alg s}

let eval_round (state round_key:quad32) =
  let s = sub_bytes state in
  let s = shift_rows s in
  let s = mix_columns s in
  let s = quad32_xor s round_key in
  s

let rec eval_rounds_def (init:quad32) (round_keys:seq quad32) (n:nat{n < length round_keys}) : quad32 =
  if n = 0 then
    init
  else
    eval_round (eval_rounds_def init round_keys (n - 1)) (index round_keys n)
[@"opaque_to_smt"] let eval_rounds = opaque_make eval_rounds_def
irreducible let eval_rounds_reveal = opaque_revealer (`%eval_rounds) eval_rounds eval_rounds_def

let eval_cipher_def (alg:algorithm) (input:quad32) (round_keys:seq quad32) : Pure quad32
  (requires length round_keys == nr alg + 1)
  (ensures fun _ -> True)
  =
  let state = quad32_xor input (index round_keys 0) in
  let state = eval_rounds_def state round_keys (nr alg - 1) in
  let state = sub_bytes state in
  let state = shift_rows state in
  let state = quad32_xor state (index round_keys (nr alg)) in
  state
[@"opaque_to_smt"] let eval_cipher = opaque_make eval_cipher_def
irreducible let eval_cipher_reveal = opaque_revealer (`%eval_cipher) eval_cipher eval_cipher_def

let rec expand_key_def (alg:algorithm) (key:aes_key_word alg) (size:nat{size <= (nb * ((nr alg) + 1))})
  : (ek:seq nat32 {length ek == size}) =
  if size = 0 then empty
  else
    let w = expand_key_def alg key (size - 1) in
    let i = size - 1 in
    if 0 <= i && i < nk alg then
      append w (create 1 (index key i))
    else
      let temp =
        if i % (nk alg) = 0 then
          nat32_xor (sub_word (rot_word (index w (i-1)))) (aes_rcon ((i / (nk alg)) - 1))
        else if nk alg > 6 && i % (nk alg) = 4 then
          sub_word (index w (i - 1))
        else
          index w (i - 1)
        in
      append w (create 1 (nat32_xor (index w (i - (nk alg))) temp))
[@"opaque_to_smt"] let expand_key = opaque_make expand_key_def
irreducible let expand_key_reveal = opaque_revealer (`%expand_key) expand_key expand_key_def

let rec key_schedule_to_round_keys (rounds:nat) (w:seq nat32 {length w >= 4 * rounds})
  : (round_keys:seq quad32 {length round_keys == rounds}) =
  if rounds = 0 then empty
  else
    let round_keys = key_schedule_to_round_keys (rounds - 1) w in
    let rk = Mkfour (index w (4 * rounds - 1)) (index w (4 * rounds - 2)) (index w (4 * rounds - 3)) (index w (4 * rounds - 4)) in
    append round_keys (create 1 rk)

[@"opaque_to_smt"]
let key_to_round_keys_word (alg:algorithm) (key:seq nat32) : Pure (seq quad32)
  (requires is_aes_key_word alg key)
  (ensures fun round_keys -> length round_keys == nr alg + 1)
  =
  key_schedule_to_round_keys (nr alg + 1) (expand_key alg key (nb * (nr alg + 1)))

let aes_encrypt_word_def (alg:algorithm) (key:seq nat32) (input:quad32) : Pure quad32
  (requires is_aes_key_word alg key)
  (ensures fun _ -> True)
  =
  eval_cipher_def alg input (key_to_round_keys_word alg key)
[@"opaque_to_smt"] let aes_encrypt_word = opaque_make aes_encrypt_word_def
irreducible let aes_encrypt_word_reveal = opaque_revealer (`%aes_encrypt_word) aes_encrypt_word aes_encrypt_word_def

#push-options "--z3rlimit 20"
let key_to_round_keys (alg:algorithm) (key:aes_key alg)
  : (round_keys:seq nat8 {length round_keys == 16 * (nr alg + 1)}) =
  let key_word = seq_nat8_to_seq_nat32_BE key in
  seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (key_to_round_keys_word alg key_word))
#pop-options

let aes_encrypt (alg:algorithm) (key:aes_key alg) (input:seq16 nat8) : seq16 nat8 =
  let key_word = seq_nat8_to_seq_nat32_BE key in
  let input = be_bytes_to_quad32 input in
  be_quad32_to_bytes (aes_encrypt_word alg key_word input)

let lemma_shl_rcon (rcon:nat8) : Lemma (ishl32 rcon 16 == ishl64 rcon 16 % pow2_32)
  =
  Vale.Def.TypesNative_s.reveal_ishl 32 rcon 16;
  FStar.UInt.shift_left_value_lemma #32 rcon 16;
  Vale.Def.TypesNative_s.reveal_ishl 64 rcon 16;
  FStar.UInt.shift_left_value_lemma #64 rcon 16
