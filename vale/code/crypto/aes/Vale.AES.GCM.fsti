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

open Vale.Def.Words.Four_s

let set_to_one_LE (q:quad32) : quad32 = four_insert q 1 0 // Mkfour 1 q.lo1 q.hi2 q.hi3 

let upper3_equal (q0 q1:quad32) : bool = 
  q0.lo1 = q1.lo1 &&
  q0.hi2 = q1.hi2 &&
  q0.hi3 = q1.hi3

let lower3_equal (q0 q1:quad32) : bool = 
  q0.lo0 = q1.lo0 &&
  q0.lo1 = q1.lo1 &&
  q0.hi2 = q1.hi2

val lemma_compute_iv_easy (iv_b iv_extra_b:seq quad32) (iv:supported_iv_LE) (num_bytes:nat64) (h_LE j0:quad32) : Lemma
  (requires
    length iv_extra_b == 1 /\
    length iv_b * (128/8) <= num_bytes /\ num_bytes < length iv_b * (128/8) + 128/8 /\
    num_bytes == 96/8 /\
    (let iv_BE = reverse_bytes_quad32 (index iv_extra_b 0) in
     j0 == Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3) /\
    (let raw_quads = append iv_b iv_extra_b in
     let iv_bytes = slice (le_seq_quad32_to_bytes raw_quads) 0 num_bytes in
     iv_bytes == iv))
  (ensures j0 == compute_iv_BE h_LE iv)

open Vale.AES.GHash
val lemma_compute_iv_hard (iv:supported_iv_LE) (quads:seq quad32) (length_quad h_LE j0:quad32) : Lemma
  (requires
    ~(length iv == 96/8) /\
    quads == le_bytes_to_seq_quad32 (pad_to_128_bits iv) /\
    j0 == ghash_incremental h_LE (Mkfour 0 0 0 0) (append quads (create 1 length_quad)) /\
    length_quad == reverse_bytes_quad32 (insert_nat64 
                                          (insert_nat64 
                                            (Mkfour 0 0 0 0) 0 1) 
                                        (8 * (length iv)) 0))
  (ensures reverse_bytes_quad32 j0 == compute_iv_BE h_LE iv)

val lemma_length_simplifier (s bytes t:seq quad32) (num_bytes:nat) : Lemma
  (requires t == (if num_bytes > (length s) * 16 then append s bytes else s) /\
            (num_bytes <= (length s) * 16 ==> num_bytes == (length s * 16)) /\
            length s * 16 <= num_bytes /\
            num_bytes < length s * 16 + 16 /\
            length bytes == 1
            )
  (ensures slice (le_seq_quad32_to_bytes t) 0 num_bytes ==
           slice (le_seq_quad32_to_bytes (append s bytes)) 0 num_bytes)

val gcm_blocks_helper_simplified (alg:algorithm) (key:seq nat32)
                   (a128 a_bytes p128x6 p128 p_bytes c128x6 c128 c_bytes:seq quad32)
                   (p_num_bytes a_num_bytes:nat)
                   (iv:supported_iv_LE) (j0_BE h enc_hash length_quad:quad32) : Lemma
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
           j0_BE == compute_iv_BE h iv /\
           h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == reverse_bytes_quad32
             (insert_nat64 (insert_nat64 (Mkfour 0 0 0 0) (8 * a_num_bytes) 1) (8 * p_num_bytes) 0) /\
          (let ctr_BE_1:quad32 = j0_BE in
           let ctr_BE_2:quad32 = inc32 j0_BE 1 in
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
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2 /\

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

           cipher_bytes == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain_bytes auth_bytes) /\
           le_quad32_to_bytes enc_hash ==
             snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key)
                                 iv plain_bytes auth_bytes))

  )

val lemma_gcm_encrypt_decrypt_equiv (alg:algorithm) (key:seq nat32) (iv:supported_iv_LE) (j0_BE:quad32) (plain cipher auth alleged_tag:seq nat8) : Lemma
  (requires
    is_aes_key_LE alg key /\
   (let h_LE = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
    j0_BE = compute_iv_BE h_LE iv) /\
    length cipher < pow2_32 /\
    length auth < pow2_32 /\
    plain == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv cipher auth)
  )
  (ensures plain == fst (gcm_decrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv cipher auth alleged_tag))

val gcm_blocks_helper_dec_simplified (alg:algorithm) (key:seq nat32)
                   (p128x6 p128 p_bytes c128x6 c128 c_bytes:seq quad32)
                   (auth_bytes alleged_tag:seq nat8)
                   (p_num_bytes:nat)
                   (iv:supported_iv_LE) (j0_BE:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128x6 * 16 + length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128x6 * 16 + length p128 * 16 + 16 /\
           length p128x6 == length c128x6 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           (length auth_bytes) < pow2_32 /\
           is_aes_key_LE alg key /\
          (let h_LE = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
           j0_BE = compute_iv_BE h_LE iv) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\
          (let ctr_BE_2:quad32 = inc32 j0_BE 1 in
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
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2
           ))
  (ensures (let plain_raw_quads = append (append p128x6 p128) p_bytes in
           let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in
           let cipher_raw_quads = append (append c128x6 c128) c_bytes in
           let cipher_bytes = slice (le_seq_quad32_to_bytes cipher_raw_quads) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           cipher_bytes == fst (gcm_decrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain_bytes auth_bytes alleged_tag)))
           

let gcm_decrypt_LE_tag (alg:algorithm) (key:seq nat8) (iv:supported_iv_LE) (cipher:seq nat8) (auth:seq nat8) :
  Pure (seq nat8)
    (requires
      is_aes_key alg key /\
      length cipher < pow2_32 /\
      length auth < pow2_32
    )
    (ensures fun t -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let h_LE = aes_encrypt_LE alg key_LE (Mkfour 0 0 0 0) in
  let j0_BE = compute_iv_BE h_LE iv in

  let lengths_BE = insert_nat64 (insert_nat64 (Mkfour 0 0 0 0) (8 * length auth) 1) (8 * length cipher) 0 in
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
                   (iv:supported_iv_LE) (j0_BE h enc_hash length_quad:quad32) : Lemma
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
           j0_BE == compute_iv_BE h iv /\

           h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == reverse_bytes_quad32
             (insert_nat64 (insert_nat64 (Mkfour 0 0 0 0) (8 * a_num_bytes) 1) (8 * p_num_bytes) 0) /\
          (let ctr_BE_1:quad32 = j0_BE in
           let ctr_BE_2:quad32 = inc32 j0_BE 1 in
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
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2 /\

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
                                                             iv plain_bytes auth_bytes))

val decrypt_helper
  (alg:algorithm) (key:seq nat8) (iv:supported_iv_LE) (cipher:seq nat8) (auth:seq nat8)
  (rax:nat64) (alleged_tag_quad computed_tag:quad32) : Lemma
  (requires
    is_aes_key alg key /\    
    length cipher < pow2_32 /\
    length auth < pow2_32 /\
    (if alleged_tag_quad = computed_tag then rax = 0 else rax > 0) /\
    le_quad32_to_bytes computed_tag == gcm_decrypt_LE_tag alg key iv cipher auth
  )
  (ensures  (rax = 0) == snd (gcm_decrypt_LE alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad)))
