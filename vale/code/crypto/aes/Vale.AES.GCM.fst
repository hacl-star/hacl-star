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

let lemma_set_to_one_equality (q0 q1:quad32) : Lemma
   (requires upper3_equal q0 q1)
   (ensures  set_to_one_LE q0 == set_to_one_LE q1)
   =
   ()
   
let lemma_set_to_one_reverse_equality (q0 q1:quad32) : Lemma
   (requires lower3_equal q0 q1)
   (ensures  set_to_one_LE (reverse_bytes_quad32 q0) == set_to_one_LE (reverse_bytes_quad32 q1))
   =
   reveal_reverse_bytes_quad32 q0;
   reveal_reverse_bytes_quad32 q1;
   ()

let lemma_le_bytes_to_quad32_prefix_equality (b0:seq nat8 {length b0 == 16}) (b1:seq nat8 {length b1 == 16}) : Lemma
  (requires slice b0 0 12 == slice b1 0 12)
  (ensures lower3_equal (le_bytes_to_quad32 b0) (le_bytes_to_quad32 b1))
  =
  let q0 = le_bytes_to_quad32 b0 in
  let q1 = le_bytes_to_quad32 b1 in
  reveal_opaque le_bytes_to_quad32_def;

  (*
   * AR: 06/25: Someone should review this code, is this proof supposed to work without revealing this?
   *)
  FStar.Pervasives.reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);

  assert (forall (i:int). (0 <= i /\ i < 12) ==> (index b0 i == index (slice b0 0 12) i /\
                                         index b1 i == index (slice b1 0 12) i))

let lemma_le_seq_quad32_to_bytes_prefix_equality (q:quad32) : Lemma
  (slice (le_quad32_to_bytes q) 0 12 == slice (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 12)) 0 12)
  =
  assert (equal (slice (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 12)) 0 12)
                (slice (le_quad32_to_bytes q) 0 12));
  ()

let lemma_compute_iv_easy (iv_b iv_extra_b:seq quad32) (iv:supported_iv_LE) (num_bytes:nat64) (h_LE j0:quad32) : Lemma
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
  =
  assert (length iv == 12);
  assert (length iv_b == 0);
  lemma_empty iv_b;
  append_empty_l iv_extra_b;
  assert (append iv_b iv_extra_b == iv_extra_b);
  let q = index iv_extra_b 0 in
  le_seq_quad32_to_bytes_of_singleton q;
  assert (equal iv_extra_b (create 1 q));
  assert (le_seq_quad32_to_bytes iv_extra_b == le_quad32_to_bytes q);

  // Prove this so we can call lemma_le_bytes_to_quad32_prefix_equality below
  calc (==) {
    slice (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 12)) 0 12;
    == {}
    slice (pad_to_128_bits iv) 0 12;
  };

  // Prove this so we can call lemma_set_to_one_reverse_equality below
  calc (==) {
    le_bytes_to_quad32 (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 num_bytes));
    == {}
    le_bytes_to_quad32 (pad_to_128_bits (slice (le_seq_quad32_to_bytes iv_extra_b) 0 num_bytes));
    == {}
    le_bytes_to_quad32 (pad_to_128_bits iv);
  };
  
  calc (==) {
    j0;
    == {}
    set_to_one_LE (reverse_bytes_quad32 q);
    == {  le_bytes_to_quad32_to_bytes q }
    set_to_one_LE (reverse_bytes_quad32 (le_bytes_to_quad32 (le_quad32_to_bytes q)));
    == { 
         lemma_le_seq_quad32_to_bytes_prefix_equality q;
         lemma_le_bytes_to_quad32_prefix_equality 
           (le_quad32_to_bytes q)
           (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 12));
         lemma_set_to_one_reverse_equality
           (le_bytes_to_quad32 (le_quad32_to_bytes q))
           (le_bytes_to_quad32 (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 12)))           
       }
    set_to_one_LE (reverse_bytes_quad32 (le_bytes_to_quad32 (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 12))));
    == { lemma_set_to_one_reverse_equality 
           (le_bytes_to_quad32 (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 12))) 
           (le_bytes_to_quad32 (pad_to_128_bits iv));
         lemma_le_bytes_to_quad32_prefix_equality 
           (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 12)) 
           (pad_to_128_bits iv) }
    set_to_one_LE (reverse_bytes_quad32 (le_bytes_to_quad32 (pad_to_128_bits iv)));
    == {}
    compute_iv_BE h_LE iv;
  };
  ()

open Vale.AES.GHash
let lemma_compute_iv_hard (iv:supported_iv_LE) (quads:seq quad32) (length_quad h_LE j0:quad32) : Lemma
  (requires
    ~(length iv == 96/8) /\
    quads == le_bytes_to_seq_quad32 (pad_to_128_bits iv) /\
    j0 == ghash_incremental h_LE (Mkfour 0 0 0 0) (append quads (create 1 length_quad)) /\
    length_quad == reverse_bytes_quad32 (insert_nat64_opaque 
                                          (insert_nat64_opaque 
                                            (Mkfour 0 0 0 0) 0 1) 
                                        (8 * (length iv)) 0))

    
    

  (ensures reverse_bytes_quad32 j0 == compute_iv_BE h_LE iv)
  =
  assert (two_to_nat32 (Mktwo 0 0) == 0);
  let q0 = Mkfour 0 0 0 0 in
  lemma_insert_nat64_nat32s q0 0 0;
  assert (insert_nat64_opaque q0 0 1 == q0);
  reveal_opaque insert_nat64;
  assert (length_quad == reverse_bytes_quad32 (insert_nat64 (Mkfour 0 0 0 0) (8 * length iv) 0));
  ghash_incremental_to_ghash h_LE (append quads (create 1 length_quad));
  ()

let gcm_encrypt_LE_fst_helper (iv:supported_iv_LE) (iv_enc iv_BE:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:seq nat32) : Lemma
  (requires
    is_aes_key_LE alg key /\
   (let h_LE = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
    iv_enc == inc32 (compute_iv_BE h_LE iv) 1 /\
    cipher == gctr_encrypt_LE iv_enc (make_gctr_plain_LE plain) alg key /\
    length plain < pow2_32 /\
    length auth < pow2_32
  ))
  (ensures cipher == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain auth))
  =
  reveal_opaque (gcm_encrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) iv plain auth)
(*
  let s_key_LE = seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE key) in
  let s_iv_BE = be_bytes_to_quad32 (be_quad32_to_bytes iv_BE) in
  let s_j0_BE = Mkfour 1 s_iv_BE.lo1 s_iv_BE.hi2 s_iv_BE.hi3 in
  let s_cipher = fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) in
  be_bytes_to_quad32_to_bytes iv_BE;
  assert (s_cipher == gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg s_key_LE);
  assert (s_iv_BE == iv_BE);
  assert (s_key_LE == key);

  assert (gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg s_key_LE ==
          gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg key);
   assert (gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg key ==
           gctr_encrypt_LE (inc32 s_j0_BE 1) (make_gctr_plain_LE plain) alg key);
  assert (gctr_encrypt_LE (inc32 s_j0_BE 1) (make_gctr_plain_LE plain) alg key ==
          gctr_encrypt_LE iv_enc (make_gctr_plain_LE plain) alg key);
  ()
*)

let gcm_encrypt_LE_snd_helper (iv:supported_iv_LE) (j0_BE length_quad32 hash mac:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:seq nat32) : Lemma
  (requires
    is_aes_key_LE alg key /\
   (let h_LE = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
    j0_BE = compute_iv_BE h_LE iv /\
    length plain < pow2_32 /\
    length auth < pow2_32 /\
    cipher == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain auth) /\
    length_quad32 == reverse_bytes_quad32
      (insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * length auth) 1) (8 * length plain) 0) /\
     (let auth_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in
      let cipher_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
      hash == ghash_LE h_LE (append auth_padded_quads (append cipher_padded_quads (create 1 length_quad32))) /\
      le_quad32_to_bytes mac == gctr_encrypt_LE j0_BE (le_quad32_to_bytes hash) alg key)
  ))
  (ensures le_quad32_to_bytes mac == snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain auth))
  =
  reveal_opaque insert_nat64;
  reveal_opaque (gcm_encrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) iv plain auth)
  //be_bytes_to_quad32_to_bytes iv_BE;
  //let t = snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) in
  //()


#reset-options "--z3rlimit 10"
let gcm_blocks_helper_enc (alg:algorithm) (key:seq nat32)
                   (p128x6 p128 p_bytes c128x6 c128 c_bytes:seq quad32)
                   (auth_bytes:seq nat8)
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
           j0_BE = compute_iv_BE h_LE iv /\

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
           gctr_partial_opaque alg cipher_bound plain cipher key ctr_BE_2
           )))
  (ensures (let plain:seq quad32 =
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
           let ctr_BE_2:quad32 = inc32 j0_BE 1 in
           let plain_bytes = slice (le_seq_quad32_to_bytes plain) 0 p_num_bytes in
           let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 p_num_bytes in
           //cipher_bytes == gctr_encrypt_LE ctr_BE_2 plain_bytes alg key))
           cipher_bytes == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain_bytes auth_bytes)))
  =
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
  let plain_bytes = slice (le_seq_quad32_to_bytes plain) 0 p_num_bytes in
  let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 p_num_bytes in
  gctr_partial_opaque_completed alg plain cipher key ctr_BE_2;
  if p_num_bytes > (length p128x6 + length p128) * 16 then (
    reveal_opaque gctr_partial;
    assert (gctr_partial_opaque alg (length p128x6 + length p128) plain cipher key ctr_BE_2);
    assert (equal (slice plain 0 (length p128x6 + length p128))
                  (slice (append p128x6 p128) 0 (length p128x6 + length p128)));
    assert (equal (slice cipher 0 (length p128x6 + length p128))
                  (slice (append c128x6 c128) 0 (length p128x6 + length p128)));
    gctr_partial_opaque_ignores_postfix
      alg (length p128x6 + length p128)
      plain (append p128x6 p128)
      cipher (append c128x6 c128)
      key ctr_BE_2;
    assert (gctr_partial_opaque alg (length p128x6 + length p128) (append p128x6 p128) (append c128x6 c128) key ctr_BE_2);
    gctr_partial_opaque_completed alg (append p128x6 p128) (append c128x6 c128) key ctr_BE_2;
    let num_blocks = p_num_bytes / 16 in
    assert(index cipher num_blocks == quad32_xor (index plain num_blocks) (aes_encrypt_BE alg key (inc32 ctr_BE_2 num_blocks)));
    gctr_encrypt_block_offset ctr_BE_2 (index plain num_blocks) alg key num_blocks;
    assert( gctr_encrypt_block ctr_BE_2 (index plain num_blocks) alg key num_blocks ==
            gctr_encrypt_block (inc32 ctr_BE_2 num_blocks) (index plain num_blocks) alg key 0);
    FStar.Pervasives.reveal_opaque (`%aes_encrypt_le) aes_encrypt_le;
    gctr_partial_to_full_advanced ctr_BE_2 plain cipher alg key p_num_bytes;
    assert (cipher_bytes == gctr_encrypt_LE ctr_BE_2 plain_bytes alg key)
  ) else (
    gctr_partial_to_full_basic ctr_BE_2 plain alg key cipher;
    assert (le_seq_quad32_to_bytes cipher == gctr_encrypt_LE ctr_BE_2 (le_seq_quad32_to_bytes plain) alg key);
    let plain_bytes = slice (le_seq_quad32_to_bytes plain) 0 p_num_bytes in
    let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 p_num_bytes in
    assert (equal plain_bytes (le_seq_quad32_to_bytes plain));
    assert (equal cipher_bytes (le_seq_quad32_to_bytes cipher));
    assert (cipher_bytes == gctr_encrypt_LE ctr_BE_2 plain_bytes alg key)
  );
  gcm_encrypt_LE_fst_helper iv ctr_BE_2 j0_BE plain_bytes auth_bytes cipher_bytes alg key;
  ()


let slice_append_back (#a:Type) (x y:seq a) (i:nat) : Lemma
  (requires length x <= i /\ i <= length x + length y)
  (ensures slice (append x y) 0 i == append x (slice y 0 (i - length x)))
  =
  assert (equal (slice (append x y) 0 i) (append x (slice y 0 (i - length x))));
  ()

let append_distributes_le_seq_quad32_to_bytes (x y:seq quad32) :
  Lemma (le_seq_quad32_to_bytes (append x y) == append (le_seq_quad32_to_bytes x) (le_seq_quad32_to_bytes y))
  =
  append_distributes_le_seq_quad32_to_bytes x y

let pad_to_128_bits_multiple_append (x y:seq nat8) : Lemma
  (requires length x % 16 == 0)
  (ensures pad_to_128_bits (append x y) == append x (pad_to_128_bits y))
  =
  assert (equal (pad_to_128_bits (append x y)) (append x (pad_to_128_bits y)))

#reset-options "--z3rlimit 100"
let gcm_blocks_helper (alg:algorithm) (key:seq nat32)
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
           j0_BE = compute_iv_BE h iv /\

           h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == reverse_bytes_quad32
             (insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * a_num_bytes) 1) (8 * p_num_bytes) 0) /\
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
  (ensures (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in
           let auth_bytes = slice (le_seq_quad32_to_bytes auth_raw_quads) 0 a_num_bytes in
           let plain_raw_quads =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               append (append p128x6 p128) p_bytes
             else append p128x6 p128
           in
           let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in

           let cipher:seq quad32 =
               if p_num_bytes > (length p128x6 + length p128) * 16 then
                  append (append c128x6 c128) c_bytes
               else
                append c128x6 c128
           in
           let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           cipher_bytes == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain_bytes auth_bytes) /\
           le_quad32_to_bytes enc_hash ==
             snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key)
                                 iv plain_bytes auth_bytes)))
  =
  let ctr_BE_1:quad32 = j0_BE in
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
  let plain_bytes = slice (le_seq_quad32_to_bytes plain) 0 p_num_bytes in
  let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 p_num_bytes in
  let auth_raw_quads =
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
  let hash = ghash_LE h final_quads in

  gcm_blocks_helper_enc alg key p128x6 p128 p_bytes c128x6 c128 c_bytes auth_input_bytes p_num_bytes iv j0_BE;
  //assert (cipher_bytes == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain_bytes auth_input_bytes)); // Passes

  calc (==) {
      enc_hash;
      == {}
      gctr_encrypt_block ctr_BE_1 (ghash_LE h final_quads) alg key 0;
      == {}
      gctr_encrypt_block ctr_BE_1 hash alg key 0;
      == {}
      quad32_xor hash (aes_encrypt_LE alg key (reverse_bytes_quad32 ctr_BE_1));
      == { FStar.Pervasives.reveal_opaque (`%aes_encrypt_le) aes_encrypt_le }
      quad32_xor hash (aes_encrypt_le alg key (reverse_bytes_quad32 ctr_BE_1));
      == {}
      quad32_xor hash (aes_encrypt_BE alg key ctr_BE_1);
    };

    calc (==) {
      gctr_encrypt_LE ctr_BE_1 (le_quad32_to_bytes hash) alg key;
      == { gctr_encrypt_one_block ctr_BE_1 hash alg key }
      le_seq_quad32_to_bytes (create 1 (quad32_xor hash (aes_encrypt_BE alg key ctr_BE_1)));
      == {}
      le_seq_quad32_to_bytes (create 1 enc_hash);
      == { le_seq_quad32_to_bytes_of_singleton enc_hash }
      le_quad32_to_bytes enc_hash;
    };


  if p_num_bytes > (length p128x6 + length p128) * 16 then (
    let c = append (append c128x6 c128) c_bytes in
    calc (==) {
      append (append (append auth_quads c128x6) c128) c_bytes;
        == { append_assoc auth_quads c128x6 c128 }
      append (append auth_quads (append c128x6 c128)) c_bytes;
        == { append_assoc auth_quads (append c128x6 c128) c_bytes }
      append auth_quads (append (append c128x6 c128) c_bytes);
        == {}
      append auth_quads c;
    };

    calc (==) {
      append (append (append (append auth_quads c128x6) c128) c_bytes) (create 1 length_quad);
        = {} // See previous calc
      append (append auth_quads (append (append c128x6 c128) c_bytes)) (create 1 length_quad);
        == { append_assoc auth_quads c (create 1 length_quad) }
      append auth_quads (append c (create 1 length_quad));
    };

    let raw_quads_old = append auth_quads c in
    calc (==) {
      raw_quads;
        == {}
      le_bytes_to_seq_quad32 (pad_to_128_bits (slice (le_seq_quad32_to_bytes raw_quads_old) 0 total_bytes));
        == {
          calc (==) {
            pad_to_128_bits (slice (le_seq_quad32_to_bytes raw_quads_old) 0 total_bytes);
              == {
                   calc (==) {
                     slice (le_seq_quad32_to_bytes raw_quads_old) 0 total_bytes;
                       == { append_distributes_le_seq_quad32_to_bytes auth_quads c }
                     slice (append (le_seq_quad32_to_bytes auth_quads) (le_seq_quad32_to_bytes c)) 0 total_bytes;
                       == { slice_append_back (le_seq_quad32_to_bytes auth_quads)
                                            (le_seq_quad32_to_bytes c)
                                            total_bytes }
                     append (le_seq_quad32_to_bytes auth_quads) (slice (le_seq_quad32_to_bytes c) 0 p_num_bytes);
                       == {}
                     append (le_seq_quad32_to_bytes auth_quads) cipher_bytes;
                   }
                 }
            pad_to_128_bits (append (le_seq_quad32_to_bytes auth_quads) cipher_bytes);
              == { pad_to_128_bits_multiple_append (le_seq_quad32_to_bytes auth_quads) cipher_bytes }
            append (le_seq_quad32_to_bytes auth_quads) (pad_to_128_bits cipher_bytes);
          }
        }
      le_bytes_to_seq_quad32 (append (le_seq_quad32_to_bytes auth_quads) (pad_to_128_bits cipher_bytes));
        == { append_distributes_le_bytes_to_seq_quad32
               (le_seq_quad32_to_bytes auth_quads)
               (pad_to_128_bits cipher_bytes) }
      append (le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes auth_quads)) (le_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes));
        == { le_bytes_to_seq_quad32_to_bytes auth_quads }
      append auth_quads (le_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes));
    };

    let auth_padded_quads' = le_bytes_to_seq_quad32 (pad_to_128_bits auth_input_bytes) in
    let cipher_padded_quads' = le_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes) in

    calc (==) {
      append raw_quads (create 1 length_quad);
        == {}
      append (append auth_quads (le_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes))) (create 1 length_quad);
        == { assert (equal auth_quads auth_padded_quads') }
      append (append auth_padded_quads' cipher_padded_quads') (create 1 length_quad);
        == { append_assoc auth_padded_quads' cipher_padded_quads' (create 1 length_quad) }
      append auth_padded_quads' (append cipher_padded_quads' (create 1 length_quad));
    };
    reveal_opaque insert_nat64;
    gcm_encrypt_LE_snd_helper iv j0_BE length_quad hash enc_hash plain_bytes auth_input_bytes cipher_bytes alg key;
    ()
  ) else (
    calc (==) {
      append (append (append auth_quads c128x6) c128) (create 1 length_quad);
        == { append_assoc auth_quads c128x6 c128 }
      append (append auth_quads (append c128x6 c128)) (create 1 length_quad);
        == { append_assoc auth_quads (append c128x6 c128) (create 1 length_quad) }
      append auth_quads (append (append c128x6 c128) (create 1 length_quad));
    };
    let c = append c128x6 c128 in
    calc (==) {
      le_bytes_to_seq_quad32 (pad_to_128_bits (slice (le_seq_quad32_to_bytes c) 0 p_num_bytes));
      == { assert (equal (le_seq_quad32_to_bytes c) (slice (le_seq_quad32_to_bytes c) 0 p_num_bytes)) }
      le_bytes_to_seq_quad32 (pad_to_128_bits (le_seq_quad32_to_bytes c));
      == { assert (pad_to_128_bits (le_seq_quad32_to_bytes c) == (le_seq_quad32_to_bytes c)) }
      le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes c);
      == { le_bytes_to_seq_quad32_to_bytes c }
      c;
    };
    reveal_opaque insert_nat64;
    gcm_encrypt_LE_snd_helper iv j0_BE length_quad hash enc_hash plain_bytes auth_input_bytes cipher_bytes alg key;
    ()
  );
  ()

// TODO: remove duplicate code -- there is an identical copy of this in GCTR.fst
let lemma_length_simplifier (s bytes t:seq quad32) (num_bytes:nat) : Lemma
  (requires t == (if num_bytes > (length s) * 16 then append s bytes else s) /\
            (num_bytes <= (length s) * 16 ==> num_bytes == (length s * 16)) /\
            length s * 16 <= num_bytes /\
            num_bytes < length s * 16 + 16 /\
            length bytes == 1
            )
  (ensures slice (le_seq_quad32_to_bytes t) 0 num_bytes ==
           slice (le_seq_quad32_to_bytes (append s bytes)) 0 num_bytes)
  =
  if num_bytes > (length s) * 16 then (
    ()
  ) else (
    calc (==) {
        slice (le_seq_quad32_to_bytes (append s bytes)) 0 num_bytes;
          == { append_distributes_le_seq_quad32_to_bytes s bytes }
        slice (append (le_seq_quad32_to_bytes s) (le_seq_quad32_to_bytes bytes)) 0 num_bytes;
          == { Vale.Lib.Seqs.lemma_slice_first_exactly_in_append (le_seq_quad32_to_bytes s) (le_seq_quad32_to_bytes bytes) }
        le_seq_quad32_to_bytes s;
          == { assert (length (le_seq_quad32_to_bytes s) == num_bytes) }
        slice (le_seq_quad32_to_bytes s) 0 num_bytes;
    };
    ()
  )

#reset-options "--z3rlimit 10"
let gcm_blocks_helper_simplified (alg:algorithm) (key:seq nat32)
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
             (insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * a_num_bytes) 1) (8 * p_num_bytes) 0) /\
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

           cipher_bytes == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain_bytes auth_bytes) /\
           le_quad32_to_bytes enc_hash ==
             snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key)
                                 iv plain_bytes auth_bytes))

  )
  =
  gcm_blocks_helper alg key a128 a_bytes p128x6 p128 p_bytes c128x6 c128 c_bytes p_num_bytes a_num_bytes iv j0_BE h enc_hash length_quad;
  let auth_raw_quads = if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128 in
  let plain_raw_quads =
    if p_num_bytes > (length p128x6 + length p128) * 16 then
     append (append p128x6 p128) p_bytes
    else append p128x6 p128
  in

  let cipher_raw_quads:seq quad32 =
    if p_num_bytes > (length p128x6 + length p128) * 16 then
      append (append c128x6 c128) c_bytes
    else
    append c128x6 c128
  in
  lemma_length_simplifier a128                 a_bytes auth_raw_quads   a_num_bytes;
  lemma_length_simplifier (append p128x6 p128) p_bytes plain_raw_quads  p_num_bytes;
  lemma_length_simplifier (append c128x6 c128) c_bytes cipher_raw_quads p_num_bytes;
  ()


let lemma_gcm_encrypt_decrypt_equiv (alg:algorithm) (key:seq nat32) (iv:supported_iv_LE) (j0_BE:quad32) (plain cipher auth alleged_tag:seq nat8) : Lemma
  (requires
    is_aes_key_LE alg key /\
   (let h_LE = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
    j0_BE = compute_iv_BE h_LE iv) /\
    length cipher < pow2_32 /\
    length auth < pow2_32 /\
    plain == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv cipher auth)
  )
  (ensures plain == fst (gcm_decrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv cipher auth alleged_tag))
  =
  reveal_opaque (gcm_encrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) iv cipher auth);
  reveal_opaque (gcm_decrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) iv cipher auth alleged_tag);
  ()


let gcm_blocks_helper_dec_simplified (alg:algorithm) (key:seq nat32)
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
           gctr_partial_opaque alg cipher_bound plain cipher key ctr_BE_2
           ))
  (ensures (let plain_raw_quads = append (append p128x6 p128) p_bytes in
           let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in
           let cipher_raw_quads = append (append c128x6 c128) c_bytes in
           let cipher_bytes = slice (le_seq_quad32_to_bytes cipher_raw_quads) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           cipher_bytes == fst (gcm_decrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain_bytes auth_bytes alleged_tag)))
  =
  gcm_blocks_helper_enc alg key p128x6 p128 p_bytes c128x6 c128 c_bytes auth_bytes p_num_bytes iv j0_BE;
  let plain_raw_quads =
    if p_num_bytes > (length p128x6 + length p128) * 16 then
     append (append p128x6 p128) p_bytes
    else append p128x6 p128
  in
  let cipher_raw_quads:seq quad32 =
    if p_num_bytes > (length p128x6 + length p128) * 16 then
      append (append c128x6 c128) c_bytes
    else
    append c128x6 c128
  in
  lemma_length_simplifier (append p128x6 p128) p_bytes plain_raw_quads  p_num_bytes;
  lemma_length_simplifier (append c128x6 c128) c_bytes cipher_raw_quads p_num_bytes;
  let plain_raw_quads = append (append p128x6 p128) p_bytes in
  let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in
  let cipher_raw_quads = append (append c128x6 c128) c_bytes in
  let cipher_bytes = slice (le_seq_quad32_to_bytes cipher_raw_quads) 0 p_num_bytes in
  assert (cipher_bytes == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) iv plain_bytes auth_bytes));
  lemma_gcm_encrypt_decrypt_equiv alg key iv j0_BE cipher_bytes plain_bytes auth_bytes alleged_tag;
  ()

#reset-options "--z3rlimit 60"
let gcm_blocks_dec_helper (alg:algorithm) (key:seq nat32)
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
           j0_BE = compute_iv_BE h iv /\
           h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == reverse_bytes_quad32
             (insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * a_num_bytes) 1) (8 * p_num_bytes) 0) /\
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
  (ensures (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in
           let auth_bytes = slice (le_seq_quad32_to_bytes auth_raw_quads) 0 a_num_bytes in
           let plain_raw_quads =
             if p_num_bytes > (length p128x6 + length p128) * 16 then
               append (append p128x6 p128) p_bytes
             else append p128x6 p128
           in
           let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in

           let cipher:seq quad32 =
               if p_num_bytes > (length p128x6 + length p128) * 16 then
                  append (append c128x6 c128) c_bytes
               else
                append c128x6 c128
           in
           let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           le_quad32_to_bytes enc_hash == gcm_decrypt_LE_tag alg (seq_nat32_to_seq_nat8_LE key)
                                 iv plain_bytes auth_bytes))
  =
  reveal_opaque insert_nat64;
  let ctr_BE_1:quad32 = j0_BE in
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
  let plain_bytes = slice (le_seq_quad32_to_bytes plain) 0 p_num_bytes in
  let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 p_num_bytes in
  let auth_raw_quads =
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
  let hash = ghash_LE h final_quads in

  //gcm_blocks_helper_enc alg key p128x6 p128 p_bytes c128x6 c128 c_bytes auth_input_bytes p_num_bytes j0_BE;
  //assert (cipher_bytes == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes j0_BE) plain_bytes auth_input_bytes)); // Passes

  calc (==) {
      enc_hash;
      == {}
      gctr_encrypt_block ctr_BE_1 (ghash_LE h final_quads) alg key 0;
      == {}
      gctr_encrypt_block ctr_BE_1 hash alg key 0;
      == {}
      quad32_xor hash (aes_encrypt_LE alg key (reverse_bytes_quad32 ctr_BE_1));
      == { FStar.Pervasives.reveal_opaque (`%aes_encrypt_le) aes_encrypt_le }
      quad32_xor hash (aes_encrypt_le alg key (reverse_bytes_quad32 ctr_BE_1));
      == {}
      quad32_xor hash (aes_encrypt_BE alg key ctr_BE_1);
    };

    calc (==) {
      gctr_encrypt_LE ctr_BE_1 (le_quad32_to_bytes hash) alg key;
      == { gctr_encrypt_one_block ctr_BE_1 hash alg key }
      le_seq_quad32_to_bytes (create 1 (quad32_xor hash (aes_encrypt_BE alg key ctr_BE_1)));
      == {}
      le_seq_quad32_to_bytes (create 1 enc_hash);
      == { le_seq_quad32_to_bytes_of_singleton enc_hash }
      le_quad32_to_bytes enc_hash;
    };

  if p_num_bytes > (length p128x6 + length p128) * 16 then (
    let c = append (append p128x6 p128) p_bytes in
    calc (==) {
      append (append (append auth_quads p128x6) p128) p_bytes;
        == { append_assoc auth_quads p128x6 p128 }
      append (append auth_quads (append p128x6 p128)) p_bytes;
        == { append_assoc auth_quads (append p128x6 p128) p_bytes }
      append auth_quads (append (append p128x6 p128) p_bytes);
        == {}
      append auth_quads c;
    };

    calc (==) {
      append (append (append (append auth_quads p128x6) p128) p_bytes) (create 1 length_quad);
        = {} // See previous calc
      append (append auth_quads (append (append p128x6 p128) p_bytes)) (create 1 length_quad);
        == { append_assoc auth_quads c (create 1 length_quad) }
      append auth_quads (append c (create 1 length_quad));
    };

    let raw_quads_old = append auth_quads c in
    calc (==) {
      raw_quads;
        == {}
      le_bytes_to_seq_quad32 (pad_to_128_bits (slice (le_seq_quad32_to_bytes raw_quads_old) 0 total_bytes));
        == {
          calc (==) {
            pad_to_128_bits (slice (le_seq_quad32_to_bytes raw_quads_old) 0 total_bytes);
              == {
                   calc (==) {
                     slice (le_seq_quad32_to_bytes raw_quads_old) 0 total_bytes;
                       == { append_distributes_le_seq_quad32_to_bytes auth_quads c }
                     slice (append (le_seq_quad32_to_bytes auth_quads) (le_seq_quad32_to_bytes c)) 0 total_bytes;
                       == { slice_append_back (le_seq_quad32_to_bytes auth_quads)
                                              (le_seq_quad32_to_bytes c)
                                              total_bytes }
                     append (le_seq_quad32_to_bytes auth_quads) (slice (le_seq_quad32_to_bytes c) 0 p_num_bytes);
                       == { assert(equal (slice (le_seq_quad32_to_bytes c) 0 p_num_bytes) plain_bytes) }
                     append (le_seq_quad32_to_bytes auth_quads) plain_bytes;
                   }
                 }
            pad_to_128_bits (append (le_seq_quad32_to_bytes auth_quads) plain_bytes);
              == { pad_to_128_bits_multiple_append (le_seq_quad32_to_bytes auth_quads) plain_bytes }
            append (le_seq_quad32_to_bytes auth_quads) (pad_to_128_bits plain_bytes);
          }
        }
      le_bytes_to_seq_quad32 (append (le_seq_quad32_to_bytes auth_quads) (pad_to_128_bits plain_bytes));
        == { append_distributes_le_bytes_to_seq_quad32
               (le_seq_quad32_to_bytes auth_quads)
               (pad_to_128_bits plain_bytes) }
      append (le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes auth_quads)) (le_bytes_to_seq_quad32 (pad_to_128_bits plain_bytes));
        == { le_bytes_to_seq_quad32_to_bytes auth_quads }
      append auth_quads (le_bytes_to_seq_quad32 (pad_to_128_bits plain_bytes));
    };


    let auth_padded_quads' = le_bytes_to_seq_quad32 (pad_to_128_bits auth_input_bytes) in
    let cipher_padded_quads' = le_bytes_to_seq_quad32 (pad_to_128_bits plain_bytes) in

    calc (==) {
      append raw_quads (create 1 length_quad);
        == {}
      append (append auth_quads (le_bytes_to_seq_quad32 (pad_to_128_bits plain_bytes))) (create 1 length_quad);
        == { assert (equal auth_quads auth_padded_quads') }
      append (append auth_padded_quads' cipher_padded_quads') (create 1 length_quad);
        == { append_assoc auth_padded_quads' cipher_padded_quads' (create 1 length_quad) }
      append auth_padded_quads' (append cipher_padded_quads' (create 1 length_quad));
    };
    ()
  ) else (
    calc (==) {
      append (append (append auth_quads p128x6) p128) (create 1 length_quad);
        == { append_assoc auth_quads p128x6 p128 }
      append (append auth_quads (append p128x6 p128)) (create 1 length_quad);
        == { append_assoc auth_quads (append p128x6 p128) (create 1 length_quad) }
      append auth_quads (append (append p128x6 p128) (create 1 length_quad));
    };
    let c = append p128x6 p128 in
    calc (==) {
      le_bytes_to_seq_quad32 (pad_to_128_bits (slice (le_seq_quad32_to_bytes c) 0 p_num_bytes));
      == { assert (equal (le_seq_quad32_to_bytes c) (slice (le_seq_quad32_to_bytes c) 0 p_num_bytes)) }
      le_bytes_to_seq_quad32 (pad_to_128_bits (le_seq_quad32_to_bytes c));
      == { assert (pad_to_128_bits (le_seq_quad32_to_bytes c) == (le_seq_quad32_to_bytes c)) }
      le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes c);
      == { le_bytes_to_seq_quad32_to_bytes c }
      c;
    };
    ()
  );
  ()

#reset-options ""
let gcm_blocks_dec_helper_simplified (alg:algorithm) (key:seq nat32)
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
             (insert_nat64_opaque (insert_nat64_opaque (Mkfour 0 0 0 0) (8 * a_num_bytes) 1) (8 * p_num_bytes) 0) /\
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
                                                             iv plain_bytes auth_bytes))
  =
  gcm_blocks_dec_helper alg key a128 a_bytes p128x6 p128 p_bytes c128x6 c128 c_bytes p_num_bytes a_num_bytes iv j0_BE h enc_hash length_quad;
  let auth_raw_quads = if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128 in
  let plain_raw_quads =
    if p_num_bytes > (length p128x6 + length p128) * 16 then
     append (append p128x6 p128) p_bytes
    else append p128x6 p128
  in

  let cipher_raw_quads:seq quad32 =
    if p_num_bytes > (length p128x6 + length p128) * 16 then
      append (append c128x6 c128) c_bytes
    else
    append c128x6 c128
  in
  lemma_length_simplifier a128                 a_bytes auth_raw_quads   a_num_bytes;
  lemma_length_simplifier (append p128x6 p128) p_bytes plain_raw_quads  p_num_bytes;
  lemma_length_simplifier (append c128x6 c128) c_bytes cipher_raw_quads p_num_bytes;
  ()

let decrypt_helper
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
  =
  reveal_opaque (gcm_decrypt_LE_def alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad));
  reveal_opaque insert_nat64;
  (*
  let b = snd (gcm_decrypt_LE alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad)) in
  let (_, ct) = gcm_decrypt_LE alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad) in

  assert (b = (ct = (le_quad32_to_bytes alleged_tag_quad)));
  assert (ct == le_quad32_to_bytes computed_tag);
  assert (b == (le_quad32_to_bytes computed_tag = le_quad32_to_bytes alleged_tag_quad));
  *)
  le_quad32_to_bytes_injective_specific alleged_tag_quad computed_tag;
  (*
  assert (b == (computed_tag = alleged_tag_quad));
  assert ((rax = 0) == (computed_tag = alleged_tag_quad));
  *)
  ()
