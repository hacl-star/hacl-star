module AEShash_stdcalls

open Vale.Stdcalls.AesHash
open Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
open Arch.Types

open Gcm_simplify
open Simplify_Sha

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


let length_aux (b:uint8_p) : Lemma
  (requires B.length b = 176)
  (ensures DV.length (get_downview b) % 16 = 0) = 
    let db = get_downview b in
    DV.length_eq db

let length_aux2 (b:uint8_p) : Lemma
  (requires B.length b = 240)
  (ensures DV.length (get_downview b) % 16 = 0) = 
    let db = get_downview b in
    DV.length_eq db

inline_for_extraction
val aes128_keyhash_init_stdcall':
  key:Ghost.erased (Seq.seq nat32) ->
  roundkeys_b:uint8_p ->
  hkeys_b:uint8_p ->
  Stack unit
    (requires fun h0 ->
      B.disjoint roundkeys_b hkeys_b /\

      B.live h0 roundkeys_b /\ B.live h0 hkeys_b /\

      B.length roundkeys_b = 176 /\
      B.length hkeys_b = 16 /\

      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (Seq.equal (B.as_seq h0 roundkeys_b)
        (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 (Ghost.reveal key))))) /\

      aesni_enabled)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_buffer hkeys_b) h0 h1 /\
  
      (let v = seq_nat8_to_seq_uint8 (le_quad32_to_bytes (reverse_bytes_quad32 (aes_encrypt_LE AES_128 (Ghost.reveal key) (Mkfour 0 0 0 0)))) in
      Seq.equal (B.as_seq h1 hkeys_b) v))

inline_for_extraction
let aes128_keyhash_init_stdcall' key roundkeys_b hkeys_b =
  let h0 = get() in

  DV.length_eq (get_downview roundkeys_b);
  DV.length_eq (get_downview hkeys_b);

  let lemma_aux1 () : Lemma
    (let db = get_downview roundkeys_b in
     length_aux roundkeys_b;
     let ub = UV.mk_buffer db Views.up_view128 in
     Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    = let db = get_downview roundkeys_b in
      let ub = UV.mk_buffer db Views.up_view128 in
      lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 roundkeys_b h0;
      Words.Seq.seq_nat8_to_seq_uint8_injective (le_seq_quad32_to_bytes (UV.as_seq h0 ub))
         (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 (Ghost.reveal key)));
      le_seq_quad32_to_bytes_injective (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key))
  in lemma_aux1 ();

  let x, _ = aes128_keyhash_init key roundkeys_b hkeys_b () in

  let h1 = get() in

  let lemma_aux2 () : Lemma
    (Seq.equal (B.as_seq h1 hkeys_b)
      (seq_nat8_to_seq_uint8 (le_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0))))
    = gcm_simplify2 hkeys_b h1
  in lemma_aux2 ()

inline_for_extraction
let aes128_keyhash_init_stdcall key roundkeys_b hkeys_b =
  let h0 = get() in
  let b_sub = B.sub hkeys_b 32ul 16ul in
  aes128_keyhash_init_stdcall' key roundkeys_b b_sub;
  let h1 = get() in
  assert (Seq.equal (Seq.slice (B.as_seq h1 hkeys_b) 0 32) (B.as_seq h1 (B.gsub hkeys_b 0ul 32ul)));
  assert (Seq.equal (Seq.slice (B.as_seq h1 hkeys_b) 48 160) (B.as_seq h1 (B.gsub hkeys_b 48ul 112ul)));
  assert (Seq.equal (Seq.slice (B.as_seq h1 hkeys_b) 0 32) (Seq.create 32 0uy));
  assert (Seq.equal (Seq.slice (B.as_seq h1 hkeys_b) 48 160) (Seq.create 112 0uy));
  assert (Seq.equal (B.as_seq h1 b_sub) (Seq.slice (B.as_seq h1 hkeys_b) 32 48))

inline_for_extraction
val aes256_keyhash_init_stdcall':
  key:Ghost.erased (Seq.seq nat32) ->
  roundkeys_b:uint8_p ->
  hkeys_b:uint8_p ->
  Stack unit
    (requires fun h0 ->
      B.disjoint roundkeys_b hkeys_b /\

      B.live h0 roundkeys_b /\ B.live h0 hkeys_b /\

      B.length roundkeys_b = 240 /\
      B.length hkeys_b = 16 /\

      is_aes_key_LE AES_256 (Ghost.reveal key) /\
      (Seq.equal (B.as_seq h0 roundkeys_b)
        (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_256 (Ghost.reveal key))))) /\

      aesni_enabled)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_buffer hkeys_b) h0 h1 /\
  
      (let v = seq_nat8_to_seq_uint8 (le_quad32_to_bytes (reverse_bytes_quad32 (aes_encrypt_LE AES_256 (Ghost.reveal key) (Mkfour 0 0 0 0)))) in
      Seq.equal (B.as_seq h1 hkeys_b) v))

inline_for_extraction
let aes256_keyhash_init_stdcall' key roundkeys_b hkeys_b =
  let h0 = get() in

  DV.length_eq (get_downview roundkeys_b);
  DV.length_eq (get_downview hkeys_b);

  let lemma_aux1 () : Lemma
    (let db = get_downview roundkeys_b in
     length_aux2 roundkeys_b;
     let ub = UV.mk_buffer db Views.up_view128 in
     Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_256 (Ghost.reveal key)))
    = let db = get_downview roundkeys_b in
      let ub = UV.mk_buffer db Views.up_view128 in
      lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 roundkeys_b h0;
      Words.Seq.seq_nat8_to_seq_uint8_injective (le_seq_quad32_to_bytes (UV.as_seq h0 ub))
         (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_256 (Ghost.reveal key)));
      le_seq_quad32_to_bytes_injective (UV.as_seq h0 ub) (key_to_round_keys_LE AES_256 (Ghost.reveal key))
  in lemma_aux1 ();

  let x, _ = aes256_keyhash_init key roundkeys_b hkeys_b () in

  let h1 = get() in

  let lemma_aux2 () : Lemma
    (Seq.equal (B.as_seq h1 hkeys_b)
      (seq_nat8_to_seq_uint8 (le_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0))))
    = gcm_simplify2 hkeys_b h1
  in lemma_aux2 ()

inline_for_extraction
let aes256_keyhash_init_stdcall key roundkeys_b hkeys_b =
  let h0 = get() in
  let b_sub = B.sub hkeys_b 32ul 16ul in
  aes256_keyhash_init_stdcall' key roundkeys_b b_sub;
  let h1 = get() in
  assert (Seq.equal (Seq.slice (B.as_seq h1 hkeys_b) 0 32) (B.as_seq h1 (B.gsub hkeys_b 0ul 32ul)));
  assert (Seq.equal (Seq.slice (B.as_seq h1 hkeys_b) 48 160) (B.as_seq h1 (B.gsub hkeys_b 48ul 112ul)));
  assert (Seq.equal (Seq.slice (B.as_seq h1 hkeys_b) 0 32) (Seq.create 32 0uy));
  assert (Seq.equal (Seq.slice (B.as_seq h1 hkeys_b) 48 160) (Seq.create 112 0uy));
  assert (Seq.equal (B.as_seq h1 b_sub) (Seq.slice (B.as_seq h1 hkeys_b) 32 48))
