module Vale.AES.GCM

open Vale.Def.Opaque_s
open Vale.Def.Types_s
open Vale.Arch.Types
open Vale.AES.GCM_s
open Vale.AES.AES_s
open Vale.AES.GCM_helpers
open Vale.AES.GCTR_s
open Vale.AES.GCTR
open Vale.AES.GHash_s
open FStar.Mul
open FStar.Seq
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open FStar.Calc

val gcm_encrypt_LE_fst_helper (iv_enc iv_BE:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:seq nat32) : Lemma
  (requires
    is_aes_key_LE alg key /\
    cipher == gctr_encrypt_LE iv_enc (make_gctr_plain_LE plain) alg key /\
    length plain < pow2_32 /\
    length auth < pow2_32 /\
    iv_enc == inc32 (Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3) 1
  )
  (ensures cipher == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth))

val gcm_encrypt_LE_snd_helper (iv_BE length_quad32 hash mac:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:seq nat32) : Lemma
  (requires
    is_aes_key_LE alg key /\
    length plain < pow2_32 /\
    length auth < pow2_32 /\
    cipher == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) /\
    length_quad32 == reverse_bytes_quad32
      (insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * length auth) 1) (8 * length plain) 0) /\
    ( let h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
      let auth_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in
      let cipher_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
      hash == ghash_LE h (append auth_padded_quads (append cipher_padded_quads (create 1 length_quad32))) /\
      le_quad32_to_bytes mac == gctr_encrypt_LE (Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3) (le_quad32_to_bytes hash) alg key)
  )
  (ensures le_quad32_to_bytes mac == snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth))


val gcm_blocks_helper_simplified (alg:algorithm) (key:seq nat32)
                   (a128 a_bytes p128x6 p128 p_bytes c128x6 c128 c_bytes:seq quad32)
                   (p_num_bytes a_num_bytes:nat)
                   (iv_BE h enc_hash length_quad:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128x6 * 16 + length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128x6 * 16 + length p128 * 16 + 16 /\
           length a128 * 16 <= a_num_bytes /\
           a_num_bytes < length a128 * 16 + 16 /\
           a_num_bytes < pow2_32 /\
           length p128x6 == length c128x6 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           length a_bytes == 1 /\
           is_aes_key_LE alg key /\

           h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == reverse_bytes_quad32
             (insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * a_num_bytes) 1) (8 * p_num_bytes) 0) /\
          (let ctr_BE_1:quad32 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
           let ctr_BE_2:quad32 = Mkfour 2 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
           let plain:seq quad32 =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               append (append p128x6 p128) p_bytes
             else
               append p128x6 p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               append (append c128x6 c128) c_bytes
             else
               append c128x6 c128
           in
           let cipher_bound:nat = length p128x6 + length p128 +
             (if p_num_bytes > (length p128x6 + length p128) * 16 then 1 else 0)
           in
           gctr_partial_opaque alg cipher_bound plain cipher key ctr_BE_2 /\

          (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in

           let auth_input_bytes = slice (le_seq_quad32_to_bytes auth_raw_quads) 0 a_num_bytes in
           let auth_padded_bytes = pad_to_128_bits auth_input_bytes in
           let auth_quads = le_bytes_to_seq_quad32 auth_padded_bytes in

           let raw_quads = append (append auth_quads c128x6) c128 in
           let total_bytes = (length auth_quads) * 16 + p_num_bytes in
           let raw_quads =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               let raw_quads = append raw_quads c_bytes in
               let input_bytes = slice (le_seq_quad32_to_bytes raw_quads) 0 total_bytes in
               let input_padded_bytes = pad_to_128_bits input_bytes in
               le_bytes_to_seq_quad32 input_padded_bytes
             else
               raw_quads
           in
           let final_quads = append raw_quads (create 1 length_quad) in
           enc_hash == gctr_encrypt_block ctr_BE_1 (ghash_LE h final_quads) alg key 0
           )))
  (ensures (let auth_raw_quads = append a128 a_bytes in
           let auth_bytes = slice (le_seq_quad32_to_bytes auth_raw_quads) 0 a_num_bytes in
           let plain_raw_quads = append (append p128x6 p128) p_bytes in
           let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in
           let cipher_raw_quads = append (append c128x6 c128) c_bytes in
           let cipher_bytes = slice (le_seq_quad32_to_bytes cipher_raw_quads) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           cipher_bytes == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain_bytes auth_bytes) /\
           le_quad32_to_bytes enc_hash ==
             snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key)
                                 (be_quad32_to_bytes iv_BE) plain_bytes auth_bytes))

  )


val lemma_gcm_encrypt_decrypt_equiv (alg:algorithm) (key:seq nat32) (iv_BE:quad32) (plain cipher auth alleged_tag:seq nat8) : Lemma
  (requires
    is_aes_key_LE alg key /\
    length cipher < pow2_32 /\
    length auth < pow2_32 /\
    plain == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) cipher auth)
  )
  (ensures plain == fst (gcm_decrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) cipher auth alleged_tag))


val gcm_blocks_helper_dec_simplified (alg:algorithm) (key:seq nat32)
                   (p128x6 p128 p_bytes c128x6 c128 c_bytes:seq quad32)
                   (auth_bytes alleged_tag:seq nat8)
                   (p_num_bytes:nat)
                   (iv_BE:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128x6 * 16 + length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128x6 * 16 + length p128 * 16 + 16 /\
           length p128x6 == length c128x6 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           (length auth_bytes) < pow2_32 /\
           is_aes_key_LE alg key /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\
          (let ctr_BE_2:quad32 = Mkfour 2 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
           let plain:seq quad32 =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               append (append p128x6 p128) p_bytes
             else
               append p128x6 p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               append (append c128x6 c128) c_bytes
             else
               append c128x6 c128
           in
           let cipher_bound:nat = length p128x6 + length p128 +
             (if p_num_bytes > (length p128x6 + length p128) * 16 then 1 else 0)
           in
           gctr_partial_opaque alg cipher_bound plain cipher key ctr_BE_2
           ))
  (ensures (let plain_raw_quads = append (append p128x6 p128) p_bytes in
           let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in
           let cipher_raw_quads = append (append c128x6 c128) c_bytes in
           let cipher_bytes = slice (le_seq_quad32_to_bytes cipher_raw_quads) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           cipher_bytes == fst (gcm_decrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain_bytes auth_bytes alleged_tag)))

let gcm_decrypt_LE_tag (alg:algorithm) (key:seq nat8) (iv:seq16 nat8) (cipher:seq nat8) (auth:seq nat8) :
  Pure (seq nat8)
    (requires
      is_aes_key alg key /\
      length cipher < pow2_32 /\
      length auth < pow2_32
    )
    (ensures fun t -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let iv_BE = be_bytes_to_quad32 iv in
  let h_LE = aes_encrypt_LE alg key_LE (Mkfour 0 0 0 0) in
  let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in

  let lengths_BE = insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * length auth) 1) (8 * length cipher) 0 in
  let lengths_LE = reverse_bytes_quad32 lengths_BE in

  let zero_padded_c_LE = le_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
  let zero_padded_a_LE = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in

  let hash_input_LE = append zero_padded_a_LE (append zero_padded_c_LE (create 1 lengths_LE)) in
  let s_LE = ghash_LE h_LE hash_input_LE in
  let t = gctr_encrypt_LE j0_BE (le_quad32_to_bytes s_LE) alg key_LE in
  t

val gcm_blocks_dec_helper_simplified (alg:algorithm) (key:seq nat32)
                   (a128 a_bytes p128x6 p128 p_bytes c128x6 c128 c_bytes:seq quad32)
                   (p_num_bytes a_num_bytes:nat)
                   (iv_BE h enc_hash length_quad:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128x6 * 16 + length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128x6 * 16 + length p128 * 16 + 16 /\
           length a128 * 16 <= a_num_bytes /\
           a_num_bytes < length a128 * 16 + 16 /\
           a_num_bytes < pow2_32 /\
           length p128x6 == length c128x6 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           length a_bytes == 1 /\
           is_aes_key_LE alg key /\

           h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == reverse_bytes_quad32
             (insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * a_num_bytes) 1) (8 * p_num_bytes) 0) /\
          (let ctr_BE_1:quad32 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
           let ctr_BE_2:quad32 = Mkfour 2 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
           let plain:seq quad32 =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               append (append p128x6 p128) p_bytes
             else
               append p128x6 p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               append (append c128x6 c128) c_bytes
             else
               append c128x6 c128
           in
           let cipher_bound:nat = length p128x6 + length p128 +
             (if p_num_bytes > (length p128x6 + length p128) * 16 then 1 else 0)
           in
           gctr_partial_opaque alg cipher_bound plain cipher key ctr_BE_2 /\

          (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in

           let auth_input_bytes = slice (le_seq_quad32_to_bytes auth_raw_quads) 0 a_num_bytes in
           let auth_padded_bytes = pad_to_128_bits auth_input_bytes in
           let auth_quads = le_bytes_to_seq_quad32 auth_padded_bytes in

           let raw_quads = append (append auth_quads p128x6) p128 in
           let total_bytes = (length auth_quads) * 16 + p_num_bytes in
           let raw_quads =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               let raw_quads = append raw_quads p_bytes in
               let input_bytes = slice (le_seq_quad32_to_bytes raw_quads) 0 total_bytes in
               let input_padded_bytes = pad_to_128_bits input_bytes in
               le_bytes_to_seq_quad32 input_padded_bytes
             else
               raw_quads
           in
           let final_quads = append raw_quads (create 1 length_quad) in
           enc_hash == gctr_encrypt_block ctr_BE_1 (ghash_LE h final_quads) alg key 0
           )))
  (ensures(let auth_raw_quads = append a128 a_bytes in
           let auth_bytes = slice (le_seq_quad32_to_bytes auth_raw_quads) 0 a_num_bytes in
           let plain_raw_quads = append (append p128x6 p128) p_bytes in
           let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in
           let cipher_raw_quads = append (append c128x6 c128) c_bytes in
           let cipher_bytes = slice (le_seq_quad32_to_bytes cipher_raw_quads) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           le_quad32_to_bytes enc_hash == gcm_decrypt_LE_tag alg (seq_nat32_to_seq_nat8_LE key)
                                                             (be_quad32_to_bytes iv_BE) plain_bytes auth_bytes))

val decrypt_helper
  (alg:algorithm) (key:seq nat8) (iv:seq16 nat8) (cipher:seq nat8) (auth:seq nat8)
  (rax:nat64) (alleged_tag_quad computed_tag:quad32) : Lemma
  (requires
    is_aes_key alg key /\
    length cipher < pow2_32 /\
    length auth < pow2_32 /\
    (if alleged_tag_quad = computed_tag then rax = 0 else rax > 0) /\
    le_quad32_to_bytes computed_tag == gcm_decrypt_LE_tag alg key iv cipher auth
  )
  (ensures  (rax = 0) == snd (gcm_decrypt_LE alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad)))
