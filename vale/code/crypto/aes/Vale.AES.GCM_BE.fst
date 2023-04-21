module Vale.AES.GCM_BE

open Vale.Def.Opaque_s
open Vale.Def.Types_s
open Vale.Arch.Types
open Vale.AES.GCM_BE_s
open Vale.AES.AES_BE_s
open Vale.AES.GCM_helpers_BE
open Vale.AES.GCTR_BE_s
open Vale.AES.GCTR_BE
open Vale.AES.GHash_BE_s
open FStar.Mul
open FStar.Seq
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open FStar.Calc

let upper3_equal (q0 q1:quad32) : bool = 
  q0.lo1 = q1.lo1 &&
  q0.hi2 = q1.hi2 &&
  q0.hi3 = q1.hi3

let lemma_be_bytes_to_quad32_prefix_equality (b0:seq nat8 {length b0 == 16}) (b1:seq nat8 {length b1 == 16}) : Lemma
  (requires slice b0 0 12 == slice b1 0 12)
  (ensures upper3_equal (be_bytes_to_quad32 b0) (be_bytes_to_quad32 b1))
  =
  let q0 = be_bytes_to_quad32 b0 in
  let q1 = be_bytes_to_quad32 b1 in
  be_bytes_to_quad32_reveal ();

  reveal_opaque (`%seq_to_seq_four_BE) (seq_to_seq_four_BE #nat8);

  assert (forall (i:int). (0 <= i /\ i < 12) ==> (index b0 i == index (slice b0 0 12) i /\
                                         index b1 i == index (slice b1 0 12) i))

let lemma_be_seq_quad32_to_bytes_prefix_equality (q:quad32) : Lemma
  (slice (be_quad32_to_bytes q) 0 12 == slice (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 12)) 0 12)
  =
  assert (equal (slice (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 12)) 0 12)
                (slice (be_quad32_to_bytes q) 0 12));
  ()

let lemma_compute_iv_easy (iv_b iv_extra_b:seq quad32) (iv:supported_iv_BE) (num_bytes:nat64) (h_BE j0:quad32) : Lemma
  (requires
    length iv_extra_b == 1 /\
    length iv_b * (128/8) <= num_bytes /\ num_bytes < length iv_b * (128/8) + 128/8 /\
    num_bytes == 96/8 /\
    (let iv_BE = index iv_extra_b 0 in
     j0 == Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3) /\
    (let raw_quads = append iv_b iv_extra_b in
     let iv_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads)) 0 num_bytes in
     iv_bytes == iv))
  (ensures j0 == compute_iv_BE h_BE iv)
  =
  assert (length iv == 12);
  assert (length iv_b == 0);
  lemma_empty iv_b;
  append_empty_l iv_extra_b;
  assert (append iv_b iv_extra_b == iv_extra_b);
  let q = index iv_extra_b 0 in
  be_seq_quad32_to_bytes_of_singleton q;
  assert (equal iv_extra_b (create 1 q));
  assert (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE iv_extra_b) == be_quad32_to_bytes q);

  calc (==) {
    slice (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 12)) 0 12;
    == {}
    slice (pad_to_128_bits iv) 0 12;
  };

  calc (==) {
    be_bytes_to_quad32 (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 num_bytes));
    == {}
    be_bytes_to_quad32 (pad_to_128_bits (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE iv_extra_b)) 0 num_bytes));
    == {}
    be_bytes_to_quad32 (pad_to_128_bits iv);
  };
  
  calc (==) {
    j0;
    == {}
    set_to_one q;
    == {  be_bytes_to_quad32_to_bytes q }
    set_to_one (be_bytes_to_quad32 (be_quad32_to_bytes q));
    == { 
         lemma_be_seq_quad32_to_bytes_prefix_equality q;
         lemma_be_bytes_to_quad32_prefix_equality 
           (be_quad32_to_bytes q)
           (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 12))
       }
    set_to_one (be_bytes_to_quad32 (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 12)));
    == { lemma_be_bytes_to_quad32_prefix_equality 
           (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 12)) 
           (pad_to_128_bits iv) }
    set_to_one (be_bytes_to_quad32 (pad_to_128_bits iv));
    == {compute_iv_BE_reveal ()}
    compute_iv_BE h_BE iv;
  };
  ()

let lemma_compute_iv_hard (iv:supported_iv_BE) (quads:seq quad32) (length_quad h_BE j0:quad32) : Lemma
  (requires
    ~(length iv == 96/8) /\
    quads == be_bytes_to_seq_quad32 (pad_to_128_bits iv) /\
    j0 == ghash_incremental h_BE (Mkfour 0 0 0 0) (append quads (create 1 length_quad)) /\
    length_quad == two_two_to_four (Mktwo (nat_to_two 32 0)
                                          (nat_to_two 32 (8 * length iv))))
  (ensures j0 == compute_iv_BE h_BE iv)
  =
  ghash_incremental_to_ghash h_BE (append quads (create 1 length_quad));
  compute_iv_BE_reveal ();
  ()

let gcm_encrypt_BE_fst_helper (iv:supported_iv_BE) (iv_enc iv_BE:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:seq nat32) : Lemma
  (requires
    is_aes_key_word alg key /\
    length plain < pow2_32 /\
    length auth < pow2_32 /\
   (let h_BE = aes_encrypt_word alg key (Mkfour 0 0 0 0) in
    iv_enc == inc32 (compute_iv_BE h_BE iv) 1 /\
    cipher == gctr_encrypt iv_enc plain alg key
  ))
  (ensures cipher == fst (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv plain auth))
  =
  gcm_encrypt_BE_reveal ()

let gcm_encrypt_BE_snd_helper (iv:supported_iv_BE) (j0_BE length_quad32 hash mac:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:seq nat32) : Lemma
  (requires
    is_aes_key_word alg key /\
    length plain < pow2_32 /\
    length auth < pow2_32 /\
   (let h_BE = aes_encrypt_word alg key (Mkfour 0 0 0 0) in
    j0_BE = compute_iv_BE h_BE iv /\
    cipher == fst (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv plain auth) /\
    length_quad32 == two_two_to_four (Mktwo (nat_to_two 32 (8 * length auth)) (nat_to_two 32 (8 * length plain))) /\
    (let auth_padded_quads = be_bytes_to_seq_quad32 (pad_to_128_bits auth) in
     let cipher_padded_quads = be_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
     hash == ghash_BE h_BE (append auth_padded_quads (append cipher_padded_quads (create 1 length_quad32))) /\
     be_quad32_to_bytes mac == gctr_encrypt j0_BE (be_quad32_to_bytes hash) alg key)
  ))
  (ensures be_quad32_to_bytes mac == snd (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv plain auth))
  =
  gcm_encrypt_BE_reveal ()

#reset-options "--z3rlimit 10"
let gcm_blocks_helper_enc (alg:algorithm) (key:seq nat32)
                   (p128 p_bytes c128 c_bytes:seq quad32)
                   (auth_bytes:seq nat8)
                   (p_num_bytes:nat)
                   (iv:supported_iv_BE) (j0_BE:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128 * 16 + 16 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           (length auth_bytes) < pow2_32 /\
           is_aes_key_word alg key /\
          (let h_BE = aes_encrypt_word alg key (Mkfour 0 0 0 0) in
           j0_BE = compute_iv_BE h_BE iv /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\
          (let ctr_BE_2:quad32 = inc32 j0_BE 1 in
           let plain:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append p128 p_bytes
             else
               p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append c128 c_bytes
             else
               c128
           in
           let cipher_bound:nat = length p128 +
             (if p_num_bytes > length p128 * 16 then 1 else 0)
           in
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2
           )))
  (ensures (let plain:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append p128 p_bytes
             else
               p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append c128 c_bytes
             else
               c128
           in
           let ctr_BE_2:quad32 = inc32 j0_BE 1 in
           let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) 0 p_num_bytes in
           let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 p_num_bytes in
           //cipher_bytes == gctr_encrypt ctr_BE_2 plain_bytes alg key))
           cipher_bytes == fst (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv plain_bytes auth_bytes)))
  =
  let ctr_BE_2:quad32 = inc32 j0_BE 1 in
  let plain:seq quad32 =
    if p_num_bytes > length p128 * 16 then
       append p128 p_bytes
    else
      p128
  in
  let cipher:seq quad32 =
    if p_num_bytes > length p128 * 16 then
       append c128 c_bytes
    else
      c128
  in
  let cipher_bound:nat = length p128 +
    (if p_num_bytes > length p128 * 16 then 1 else 0)
  in
  let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) 0 p_num_bytes in
  let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 p_num_bytes in
  gctr_partial_opaque_completed alg plain cipher key ctr_BE_2;
  if p_num_bytes > length p128 * 16 then (
    gctr_partial_reveal ();
    assert (gctr_partial alg (length p128) plain cipher key ctr_BE_2);
    assert (equal (slice plain 0 (length p128))
                  (slice p128 0 (length p128)));
    assert (equal (slice cipher 0 (length p128))
                  (slice c128 0 (length p128)));
    gctr_partial_opaque_ignores_postfix
      alg (length p128)
      plain p128
      cipher c128
      key ctr_BE_2;
    assert (gctr_partial alg (length p128) p128 c128 key ctr_BE_2);
    gctr_partial_opaque_completed alg p128 c128 key ctr_BE_2;
    let num_blocks = p_num_bytes / 16 in
    assert(index cipher num_blocks == quad32_xor (index plain num_blocks) (aes_encrypt_word alg key (inc32 ctr_BE_2 num_blocks)));
    gctr_encrypt_block_offset ctr_BE_2 (index plain num_blocks) alg key num_blocks;
    assert( gctr_encrypt_block ctr_BE_2 (index plain num_blocks) alg key num_blocks ==
            gctr_encrypt_block (inc32 ctr_BE_2 num_blocks) (index plain num_blocks) alg key 0);
    aes_encrypt_word_reveal ();
    gctr_partial_to_full_advanced ctr_BE_2 plain cipher alg key p_num_bytes;
    assert (cipher_bytes == gctr_encrypt ctr_BE_2 plain_bytes alg key)
  ) else (
    gctr_partial_to_full_basic ctr_BE_2 plain alg key cipher;
    assert (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher) == gctr_encrypt ctr_BE_2 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) alg key);
    let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) 0 p_num_bytes in
    let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 p_num_bytes in
    assert (equal plain_bytes (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)));
    assert (equal cipher_bytes (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)));
    assert (cipher_bytes == gctr_encrypt ctr_BE_2 plain_bytes alg key)
  );
  gcm_encrypt_BE_fst_helper iv ctr_BE_2 j0_BE plain_bytes auth_bytes cipher_bytes alg key;
  ()

let slice_append_back (#a:Type) (x y:seq a) (i:nat) : Lemma
  (requires length x <= i /\ i <= length x + length y)
  (ensures slice (append x y) 0 i == append x (slice y 0 (i - length x)))
  =
  assert (equal (slice (append x y) 0 i) (append x (slice y 0 (i - length x))));
  ()

let append_distributes_be_seq_quad32_to_bytes (x y:seq quad32) :
  Lemma (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (append x y)) == append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE x)) (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE y)))
  =
  append_distributes_be_seq_quad32_to_bytes x y

let pad_to_128_bits_multiple_append (x y:seq nat8) : Lemma
  (requires length x % 16 == 0)
  (ensures pad_to_128_bits (append x y) == append x (pad_to_128_bits y))
  =
  assert (equal (pad_to_128_bits (append x y)) (append x (pad_to_128_bits y)))

#reset-options "--z3rlimit 100"
let gcm_blocks_helper (alg:algorithm) (key:seq nat32)
                   (a128 a_bytes p128 p_bytes c128 c_bytes:seq quad32)
                   (p_num_bytes a_num_bytes:nat)
                   (iv:supported_iv_BE) (j0_BE h enc_hash length_quad:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128 * 16 + 16 /\
           length a128 * 16 <= a_num_bytes /\
           a_num_bytes < length a128 * 16 + 16 /\
           a_num_bytes < pow2_32 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           length a_bytes == 1 /\
           is_aes_key_word alg key /\
           j0_BE = compute_iv_BE h iv /\

           h = aes_encrypt_word alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == two_two_to_four (Mktwo (nat_to_two 32 (8 * a_num_bytes)) (nat_to_two 32 (8 * p_num_bytes))) /\
          (let ctr_BE_1:quad32 = j0_BE in
           let ctr_BE_2:quad32 = inc32 j0_BE 1 in
           let plain:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append p128 p_bytes
             else
               p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append c128 c_bytes
             else
               c128
           in
           let cipher_bound:nat = length p128 +
             (if p_num_bytes > length p128 * 16 then 1 else 0)
           in
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2 /\

          (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in

           let auth_input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
           let auth_padded_bytes = pad_to_128_bits auth_input_bytes in
           let auth_quads = be_bytes_to_seq_quad32 auth_padded_bytes in

           let raw_quads = append auth_quads c128 in
           let total_bytes = length auth_quads * 16 + p_num_bytes in
           let raw_quads =
             if p_num_bytes > length p128 * 16 then
               let raw_quads = append raw_quads c_bytes in
               let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads)) 0 total_bytes in
               let input_padded_bytes = pad_to_128_bits input_bytes in
               be_bytes_to_seq_quad32 input_padded_bytes
             else
               raw_quads
           in
           let final_quads = append raw_quads (create 1 length_quad) in
           enc_hash == gctr_encrypt_block ctr_BE_1 (ghash_BE h final_quads) alg key 0
           )))
  (ensures (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in
           let auth_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
           let plain_raw_quads =
             if p_num_bytes > length p128 * 16 then
               append p128 p_bytes
             else p128
           in
           let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain_raw_quads)) 0 p_num_bytes in

           let cipher:seq quad32 =
               if p_num_bytes > length p128 * 16 then
                  append c128 c_bytes
               else
                c128
           in
           let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           cipher_bytes == fst (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv plain_bytes auth_bytes) /\
           be_quad32_to_bytes enc_hash ==
             snd (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key)
                                 iv plain_bytes auth_bytes)))
  =
  let ctr_BE_1:quad32 = j0_BE in
  let ctr_BE_2:quad32 = inc32 j0_BE 1 in
  let plain:seq quad32 =
    if p_num_bytes > length p128 * 16 then
       append p128 p_bytes
    else
      p128
  in
  let cipher:seq quad32 =
    if p_num_bytes > length p128 * 16 then
       append c128 c_bytes
    else
      c128
  in
  let cipher_bound:nat = length p128 +
    (if p_num_bytes > length p128 * 16 then 1 else 0)
  in
  let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) 0 p_num_bytes in
  let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 p_num_bytes in
  let auth_raw_quads =
    if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
  in
  let auth_input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
  let auth_padded_bytes = pad_to_128_bits auth_input_bytes in
  let auth_quads = be_bytes_to_seq_quad32 auth_padded_bytes in

  let raw_quads = append auth_quads c128 in
  let total_bytes = length auth_quads * 16 + p_num_bytes in
  let raw_quads =
    if p_num_bytes > length p128 * 16 then
       let raw_quads = append raw_quads c_bytes in
       let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads)) 0 total_bytes in
       let input_padded_bytes = pad_to_128_bits input_bytes in
       be_bytes_to_seq_quad32 input_padded_bytes
    else
      raw_quads
  in
  let final_quads = append raw_quads (create 1 length_quad) in
  let hash = ghash_BE h final_quads in

  gcm_blocks_helper_enc alg key p128 p_bytes c128 c_bytes auth_input_bytes p_num_bytes iv j0_BE;

  calc (==) {
      enc_hash;
      == {}
      gctr_encrypt_block ctr_BE_1 (ghash_BE h final_quads) alg key 0;
      == {}
      gctr_encrypt_block ctr_BE_1 hash alg key 0;
      == {}
      quad32_xor hash (aes_encrypt_word alg key ctr_BE_1);
    };

    calc (==) {
      gctr_encrypt ctr_BE_1 (be_quad32_to_bytes hash) alg key;
      == { gctr_encrypt_one_block ctr_BE_1 hash alg key }
      seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (create 1 (quad32_xor hash (aes_encrypt_word alg key ctr_BE_1))));
      == {}
      seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (create 1 enc_hash));
      == { be_seq_quad32_to_bytes_of_singleton enc_hash }
      be_quad32_to_bytes enc_hash;
    };


  if p_num_bytes > length p128 * 16 then (
    let c = append c128 c_bytes in
    calc (==) {
      append (append auth_quads c128) c_bytes;
        == { append_assoc auth_quads c128 c_bytes }
      append auth_quads (append c128 c_bytes);
        == {}
      append auth_quads c;
    };

    calc (==) {
      append (append (append auth_quads c128) c_bytes) (create 1 length_quad);
        = {} // See previous calc
      append (append auth_quads (append c128 c_bytes)) (create 1 length_quad);
        == { append_assoc auth_quads c (create 1 length_quad) }
      append auth_quads (append c (create 1 length_quad));
    };

    let raw_quads_old = append auth_quads c in
    calc (==) {
      raw_quads;
        == {}
      be_bytes_to_seq_quad32 (pad_to_128_bits (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads_old)) 0 total_bytes));
        == {
          calc (==) {
            pad_to_128_bits (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads_old)) 0 total_bytes);
              == {
                   calc (==) {
                     slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads_old)) 0 total_bytes;
                       == { append_distributes_be_seq_quad32_to_bytes auth_quads c }
                     slice (append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c))) 0 total_bytes;
                       == { slice_append_back (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads))
                                            (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c))
                                            total_bytes }
                     append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) 0 p_num_bytes);
                       == {}
                     append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) cipher_bytes;
                   }
                 }
            pad_to_128_bits (append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) cipher_bytes);
              == { pad_to_128_bits_multiple_append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) cipher_bytes }
            append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) (pad_to_128_bits cipher_bytes);
          }
        }
      be_bytes_to_seq_quad32 (append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) (pad_to_128_bits cipher_bytes));
        == { append_distributes_be_bytes_to_seq_quad32
               (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads))
               (pad_to_128_bits cipher_bytes) }
      append (be_bytes_to_seq_quad32 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads))) (be_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes));
        == { be_bytes_to_seq_quad32_to_bytes auth_quads }
      append auth_quads (be_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes));
    };

    let auth_padded_quads' = be_bytes_to_seq_quad32 (pad_to_128_bits auth_input_bytes) in
    let cipher_padded_quads' = be_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes) in

    calc (==) {
      append raw_quads (create 1 length_quad);
        == {}
      append (append auth_quads (be_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes))) (create 1 length_quad);
        == { assert (equal auth_quads auth_padded_quads') }
      append (append auth_padded_quads' cipher_padded_quads') (create 1 length_quad);
        == { append_assoc auth_padded_quads' cipher_padded_quads' (create 1 length_quad) }
      append auth_padded_quads' (append cipher_padded_quads' (create 1 length_quad));
    };
    gcm_encrypt_BE_snd_helper iv j0_BE length_quad hash enc_hash plain_bytes auth_input_bytes cipher_bytes alg key;
    ()
  ) else (
    calc (==) {
      append (append auth_quads c128) (create 1 length_quad);
        == { append_assoc auth_quads c128 (create 1 length_quad) }
      append auth_quads (append c128 (create 1 length_quad));
    };
    let c = c128 in
    calc (==) {
      be_bytes_to_seq_quad32 (pad_to_128_bits (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) 0 p_num_bytes));
      == { assert (equal (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) 0 p_num_bytes)) }
      be_bytes_to_seq_quad32 (pad_to_128_bits (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)));
      == { assert (pad_to_128_bits (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) == (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c))) }
      be_bytes_to_seq_quad32 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c));
      == { be_bytes_to_seq_quad32_to_bytes c }
      c;
    };
    gcm_encrypt_BE_snd_helper iv j0_BE length_quad hash enc_hash plain_bytes auth_input_bytes cipher_bytes alg key;
    ()
  );
  ()

let lemma_length_simplifier (s bytes t:seq quad32) (num_bytes:nat) : Lemma
  (requires t == (if num_bytes > (length s) * 16 then append s bytes else s) /\
            (num_bytes <= (length s) * 16 ==> num_bytes == (length s * 16)) /\
            length s * 16 <= num_bytes /\
            num_bytes < length s * 16 + 16 /\
            length bytes == 1
            )
  (ensures slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE t)) 0 num_bytes ==
           slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (append s bytes))) 0 num_bytes)
  =
  if num_bytes > (length s) * 16 then (
    ()
  ) else (
    calc (==) {
        slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (append s bytes))) 0 num_bytes;
          == { append_distributes_be_seq_quad32_to_bytes s bytes }
        slice (append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE bytes))) 0 num_bytes;
          == { Vale.Lib.Seqs.lemma_slice_first_exactly_in_append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE bytes)) }
        seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s);
          == { assert (length (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) == num_bytes) }
        slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) 0 num_bytes;
    };
    ()
  )

#reset-options "--z3rlimit 10"
let gcm_blocks_helper_simplified (alg:algorithm) (key:seq nat32)
                   (a128 a_bytes p128 p_bytes c128 c_bytes:seq quad32)
                   (p_num_bytes a_num_bytes:nat)
                   (iv:supported_iv_BE) (j0_BE h enc_hash length_quad:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128 * 16 + 16 /\
           length a128 * 16 <= a_num_bytes /\
           a_num_bytes < length a128 * 16 + 16 /\
           a_num_bytes < pow2_32 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           length a_bytes == 1 /\
           is_aes_key_word alg key /\
           j0_BE == compute_iv_BE h iv /\
           h = aes_encrypt_word alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == two_two_to_four (Mktwo (nat_to_two 32 (8 * a_num_bytes)) (nat_to_two 32 (8 * p_num_bytes))) /\
          (let ctr_BE_1:quad32 = j0_BE in
           let ctr_BE_2:quad32 = inc32 j0_BE 1 in
           let plain:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append p128 p_bytes
             else
               p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append c128 c_bytes
             else
               c128
           in
           let cipher_bound:nat = length p128 +
             (if p_num_bytes > length p128 * 16 then 1 else 0)
           in
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2 /\

          (let auth_raw_quads =
             if a_num_bytes > length a128 * 16 then append a128 a_bytes else a128
           in

           let auth_input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
           let auth_padded_bytes = pad_to_128_bits auth_input_bytes in
           let auth_quads = be_bytes_to_seq_quad32 auth_padded_bytes in

           let raw_quads = append auth_quads c128 in
           let total_bytes = length auth_quads * 16 + p_num_bytes in
           let raw_quads =
             if p_num_bytes > length p128 * 16 then
               let raw_quads = append raw_quads c_bytes in
               let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads)) 0 total_bytes in
               let input_padded_bytes = pad_to_128_bits input_bytes in
               be_bytes_to_seq_quad32 input_padded_bytes
             else
               raw_quads
           in
           let final_quads = append raw_quads (create 1 length_quad) in
           enc_hash == gctr_encrypt_block ctr_BE_1 (ghash_BE h final_quads) alg key 0
           )))
  (ensures (let auth_raw_quads = append a128 a_bytes in
           let auth_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
           let plain_raw_quads = append p128 p_bytes in
           let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain_raw_quads)) 0 p_num_bytes in
           let cipher_raw_quads = append c128 c_bytes in
           let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_raw_quads)) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           cipher_bytes == fst (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv plain_bytes auth_bytes) /\
           be_quad32_to_bytes enc_hash ==
             snd (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key)
                                 iv plain_bytes auth_bytes))

  )
  =
  gcm_blocks_helper alg key a128 a_bytes p128 p_bytes c128 c_bytes p_num_bytes a_num_bytes iv j0_BE h enc_hash length_quad;
  let auth_raw_quads = if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128 in
  let plain_raw_quads =
    if p_num_bytes > length p128 * 16 then
     append p128 p_bytes
    else p128
  in

  let cipher_raw_quads:seq quad32 =
    if p_num_bytes > length p128 * 16 then
      append c128 c_bytes
    else
    c128
  in
  lemma_length_simplifier a128                 a_bytes auth_raw_quads   a_num_bytes;
  lemma_length_simplifier p128 p_bytes plain_raw_quads  p_num_bytes;
  lemma_length_simplifier c128 c_bytes cipher_raw_quads p_num_bytes;
  ()

let lemma_gcm_encrypt_decrypt_equiv (alg:algorithm) (key:seq nat32) (iv:supported_iv_BE) (j0_BE:quad32) (plain cipher auth alleged_tag:seq nat8) : Lemma
  (requires
    is_aes_key_word alg key /\
   (let h_BE = aes_encrypt_word alg key (Mkfour 0 0 0 0) in
    j0_BE = compute_iv_BE h_BE iv) /\
    length cipher < pow2_32 /\
    length auth < pow2_32 /\
    plain == fst (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv cipher auth)
  )
  (ensures plain == fst (gcm_decrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv cipher auth alleged_tag))
  =
  gcm_encrypt_BE_reveal ();
  gcm_decrypt_BE_reveal ();
  ()

let gcm_blocks_helper_dec_simplified (alg:algorithm) (key:seq nat32)
                   (p128 p_bytes c128 c_bytes:seq quad32)
                   (auth_bytes alleged_tag:seq nat8)
                   (p_num_bytes:nat)
                   (iv:supported_iv_BE) (j0_BE:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128 * 16 + 16 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           (length auth_bytes) < pow2_32 /\
           is_aes_key_word alg key /\
          (let h_BE = aes_encrypt_word alg key (Mkfour 0 0 0 0) in
           j0_BE = compute_iv_BE h_BE iv) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\
          (let ctr_BE_2:quad32 = inc32 j0_BE 1 in
           let plain:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append p128 p_bytes
             else
               p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append c128 c_bytes
             else
               c128
           in
           let cipher_bound:nat = length p128 +
             (if p_num_bytes > length p128 * 16 then 1 else 0)
           in
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2
           ))
  (ensures (let plain_raw_quads = append p128 p_bytes in
           let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain_raw_quads)) 0 p_num_bytes in
           let cipher_raw_quads = append c128 c_bytes in
           let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_raw_quads)) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           cipher_bytes == fst (gcm_decrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv plain_bytes auth_bytes alleged_tag)))
  =
  gcm_blocks_helper_enc alg key p128 p_bytes c128 c_bytes auth_bytes p_num_bytes iv j0_BE;
  let plain_raw_quads =
    if p_num_bytes > length p128 * 16 then
     append p128 p_bytes
    else p128
  in
  let cipher_raw_quads:seq quad32 =
    if p_num_bytes > length p128 * 16 then
      append c128 c_bytes
    else
    c128
  in
  lemma_length_simplifier p128 p_bytes plain_raw_quads  p_num_bytes;
  lemma_length_simplifier c128 c_bytes cipher_raw_quads p_num_bytes;
  let plain_raw_quads = append p128 p_bytes in
  let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain_raw_quads)) 0 p_num_bytes in
  let cipher_raw_quads = append c128 c_bytes in
  let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_raw_quads)) 0 p_num_bytes in
  assert (cipher_bytes == fst (gcm_encrypt_BE alg (seq_nat32_to_seq_nat8_BE key) iv plain_bytes auth_bytes));
  lemma_gcm_encrypt_decrypt_equiv alg key iv j0_BE cipher_bytes plain_bytes auth_bytes alleged_tag;
  ()

#reset-options "--z3rlimit 60"
let gcm_blocks_dec_helper (alg:algorithm) (key:seq nat32)
                   (a128 a_bytes p128 p_bytes c128 c_bytes:seq quad32)
                   (p_num_bytes a_num_bytes:nat)
                   (iv:supported_iv_BE) (j0_BE h enc_hash length_quad:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128 * 16 + 16 /\
           length a128 * 16 <= a_num_bytes /\
           a_num_bytes < length a128 * 16 + 16 /\
           a_num_bytes < pow2_32 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           length a_bytes == 1 /\
           is_aes_key_word alg key /\
           j0_BE = compute_iv_BE h iv /\
           h = aes_encrypt_word alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == two_two_to_four (Mktwo (nat_to_two 32 (8 * a_num_bytes)) (nat_to_two 32 (8 * p_num_bytes))) /\
          (let ctr_BE_1:quad32 = j0_BE in
           let ctr_BE_2:quad32 = inc32 j0_BE 1 in
           let plain:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append p128 p_bytes
             else
               p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append c128 c_bytes
             else
               c128
           in
           let cipher_bound:nat = length p128 +
             (if p_num_bytes > length p128 * 16 then 1 else 0)
           in
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2 /\

          (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in

           let auth_input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
           let auth_padded_bytes = pad_to_128_bits auth_input_bytes in
           let auth_quads = be_bytes_to_seq_quad32 auth_padded_bytes in

           let raw_quads = append auth_quads p128 in
           let total_bytes = length auth_quads * 16 + p_num_bytes in
           let raw_quads =
             if p_num_bytes > length p128 * 16 then
               let raw_quads = append raw_quads p_bytes in
               let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads)) 0 total_bytes in
               let input_padded_bytes = pad_to_128_bits input_bytes in
               be_bytes_to_seq_quad32 input_padded_bytes
             else
               raw_quads
           in
           let final_quads = append raw_quads (create 1 length_quad) in
           enc_hash == gctr_encrypt_block ctr_BE_1 (ghash_BE h final_quads) alg key 0
           )))
  (ensures (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in
           let auth_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
           let plain_raw_quads =
             if p_num_bytes >length p128 * 16 then
               append p128 p_bytes
             else p128
           in
           let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain_raw_quads)) 0 p_num_bytes in

           let cipher:seq quad32 =
               if p_num_bytes > length p128 * 16 then
                  append c128 c_bytes
               else
                c128
           in
           let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           be_quad32_to_bytes enc_hash == gcm_decrypt_BE_tag alg (seq_nat32_to_seq_nat8_BE key)
                                 iv plain_bytes auth_bytes))
  =
  let ctr_BE_1:quad32 = j0_BE in
  let ctr_BE_2:quad32 = inc32 j0_BE 1 in
  let plain:seq quad32 =
    if p_num_bytes > length p128 * 16 then
       append p128 p_bytes
    else
      p128
  in
  let cipher:seq quad32 =
    if p_num_bytes > length p128 * 16 then
       append c128 c_bytes
    else
      c128
  in
  let cipher_bound:nat = length p128 +
    (if p_num_bytes > length p128 * 16 then 1 else 0)
  in
  let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) 0 p_num_bytes in
  let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 p_num_bytes in
  let auth_raw_quads =
    if a_num_bytes > length a128 * 16 then append a128 a_bytes else a128
  in
  let auth_input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
  let auth_padded_bytes = pad_to_128_bits auth_input_bytes in
  let auth_quads = be_bytes_to_seq_quad32 auth_padded_bytes in

  let raw_quads = append auth_quads p128 in
  let total_bytes = length auth_quads * 16 + p_num_bytes in
  let raw_quads =
    if p_num_bytes > length p128 * 16 then
       let raw_quads = append raw_quads p_bytes in
       let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads)) 0 total_bytes in
       let input_padded_bytes = pad_to_128_bits input_bytes in
       be_bytes_to_seq_quad32 input_padded_bytes
    else
      raw_quads
  in
  let final_quads = append raw_quads (create 1 length_quad) in
  let hash = ghash_BE h final_quads in

  calc (==) {
      enc_hash;
      == {}
      gctr_encrypt_block ctr_BE_1 (ghash_BE h final_quads) alg key 0;
      == {}
      gctr_encrypt_block ctr_BE_1 hash alg key 0;
      == {}
      quad32_xor hash (aes_encrypt_word alg key ctr_BE_1);
    };

    calc (==) {
      gctr_encrypt ctr_BE_1 (be_quad32_to_bytes hash) alg key;
      == { gctr_encrypt_one_block ctr_BE_1 hash alg key }
      seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (create 1 (quad32_xor hash (aes_encrypt_word alg key ctr_BE_1))));
      == {}
      seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (create 1 enc_hash));
      == { be_seq_quad32_to_bytes_of_singleton enc_hash }
      be_quad32_to_bytes enc_hash;
    };

  if p_num_bytes > length p128 * 16 then (
    let c = append p128 p_bytes in
    calc (==) {
      append (append auth_quads p128) p_bytes;
        == { append_assoc auth_quads p128 p_bytes }
      append auth_quads (append p128 p_bytes);
        == {}
      append auth_quads c;
    };

    calc (==) {
      append (append (append auth_quads p128) p_bytes) (create 1 length_quad);
        = {} // See previous calc
      append (append auth_quads (append p128 p_bytes)) (create 1 length_quad);
        == { append_assoc auth_quads c (create 1 length_quad) }
      append auth_quads (append c (create 1 length_quad));
    };

    let raw_quads_old = append auth_quads c in
    calc (==) {
      raw_quads;
        == {}
      be_bytes_to_seq_quad32 (pad_to_128_bits (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads_old)) 0 total_bytes));
        == {
          calc (==) {
            pad_to_128_bits (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads_old)) 0 total_bytes);
              == {
                   calc (==) {
                     slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads_old)) 0 total_bytes;
                       == { append_distributes_be_seq_quad32_to_bytes auth_quads c }
                     slice (append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c))) 0 total_bytes;
                       == { slice_append_back (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads))
                                              (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c))
                                              total_bytes }
                     append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) 0 p_num_bytes);
                       == { assert(equal (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) 0 p_num_bytes) plain_bytes) }
                     append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) plain_bytes;
                   }
                 }
            pad_to_128_bits (append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) plain_bytes);
              == { pad_to_128_bits_multiple_append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) plain_bytes }
            append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) (pad_to_128_bits plain_bytes);
          }
        }
      be_bytes_to_seq_quad32 (append (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads)) (pad_to_128_bits plain_bytes));
        == { append_distributes_be_bytes_to_seq_quad32
               (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads))
               (pad_to_128_bits plain_bytes) }
      append (be_bytes_to_seq_quad32 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_quads))) (be_bytes_to_seq_quad32 (pad_to_128_bits plain_bytes));
        == { be_bytes_to_seq_quad32_to_bytes auth_quads }
      append auth_quads (be_bytes_to_seq_quad32 (pad_to_128_bits plain_bytes));
    };


    let auth_padded_quads' = be_bytes_to_seq_quad32 (pad_to_128_bits auth_input_bytes) in
    let cipher_padded_quads' = be_bytes_to_seq_quad32 (pad_to_128_bits plain_bytes) in

    calc (==) {
      append raw_quads (create 1 length_quad);
        == {}
      append (append auth_quads (be_bytes_to_seq_quad32 (pad_to_128_bits plain_bytes))) (create 1 length_quad);
        == { assert (equal auth_quads auth_padded_quads') }
      append (append auth_padded_quads' cipher_padded_quads') (create 1 length_quad);
        == { append_assoc auth_padded_quads' cipher_padded_quads' (create 1 length_quad) }
      append auth_padded_quads' (append cipher_padded_quads' (create 1 length_quad));
    };
    ()
  ) else (
    calc (==) {
      append (append auth_quads p128) (create 1 length_quad);
        == { append_assoc auth_quads p128 (create 1 length_quad) }
      append auth_quads (append p128 (create 1 length_quad));
    };
    let c = p128 in
    calc (==) {
      be_bytes_to_seq_quad32 (pad_to_128_bits (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) 0 p_num_bytes));
      == { assert (equal (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) 0 p_num_bytes)) }
      be_bytes_to_seq_quad32 (pad_to_128_bits (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)));
      == { assert (pad_to_128_bits (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c)) == (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c))) }
      be_bytes_to_seq_quad32 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE c));
      == { be_bytes_to_seq_quad32_to_bytes c }
      c;
    };
    ()
  );
  ()

#reset-options ""
let gcm_blocks_dec_helper_simplified (alg:algorithm) (key:seq nat32)
                   (a128 a_bytes p128 p_bytes c128 c_bytes:seq quad32)
                   (p_num_bytes a_num_bytes:nat)
                   (iv:supported_iv_BE) (j0_BE h enc_hash length_quad:quad32) : Lemma
  (requires // Required by gcm_blocks
           length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128 * 16 + 16 /\
           length a128 * 16 <= a_num_bytes /\
           a_num_bytes < length a128 * 16 + 16 /\
           a_num_bytes < pow2_32 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           length a_bytes == 1 /\
           is_aes_key_word alg key /\
           j0_BE == compute_iv_BE h iv /\

           h = aes_encrypt_word alg key (Mkfour 0 0 0 0) /\

           // Ensured by gcm_blocks
           p_num_bytes < pow2_32 /\ a_num_bytes < pow2_32 /\
           length_quad == two_two_to_four (Mktwo (nat_to_two 32 (8 * a_num_bytes)) (nat_to_two 32 (8 * p_num_bytes))) /\
          (let ctr_BE_1:quad32 = j0_BE in
           let ctr_BE_2:quad32 = inc32 j0_BE 1 in
           let plain:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append p128 p_bytes
             else
               p128
           in
           let cipher:seq quad32 =
             if p_num_bytes > length p128 * 16 then
               append c128 c_bytes
             else
               c128
           in
           let cipher_bound:nat = length p128 +
             (if p_num_bytes > length p128 * 16 then 1 else 0)
           in
           gctr_partial alg cipher_bound plain cipher key ctr_BE_2 /\

          (let auth_raw_quads =
             if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128
           in

           let auth_input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
           let auth_padded_bytes = pad_to_128_bits auth_input_bytes in
           let auth_quads = be_bytes_to_seq_quad32 auth_padded_bytes in

           let raw_quads = append auth_quads p128 in
           let total_bytes = (length auth_quads) * 16 + p_num_bytes in
           let raw_quads =
             if p_num_bytes > length p128 * 16 then
               let raw_quads = append raw_quads p_bytes in
               let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE raw_quads)) 0 total_bytes in
               let input_padded_bytes = pad_to_128_bits input_bytes in
               be_bytes_to_seq_quad32 input_padded_bytes
             else
               raw_quads
           in
           let final_quads = append raw_quads (create 1 length_quad) in
           enc_hash == gctr_encrypt_block ctr_BE_1 (ghash_BE h final_quads) alg key 0
           )))
  (ensures(let auth_raw_quads = append a128 a_bytes in
           let auth_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE auth_raw_quads)) 0 a_num_bytes in
           let plain_raw_quads = append p128 p_bytes in
           let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain_raw_quads)) 0 p_num_bytes in
           let cipher_raw_quads = append c128 c_bytes in
           let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_raw_quads)) 0 p_num_bytes in

           length auth_bytes < pow2_32 /\
           length plain_bytes < pow2_32 /\

           be_quad32_to_bytes enc_hash == gcm_decrypt_BE_tag alg (seq_nat32_to_seq_nat8_BE key)
                                                             iv plain_bytes auth_bytes))
  =
  gcm_blocks_dec_helper alg key a128 a_bytes p128 p_bytes c128 c_bytes p_num_bytes a_num_bytes iv j0_BE h enc_hash length_quad;
  let auth_raw_quads = if a_num_bytes > (length a128) * 16 then append a128 a_bytes else a128 in
  let plain_raw_quads =
    if p_num_bytes > length p128 * 16 then
     append p128 p_bytes
    else p128
  in

  let cipher_raw_quads:seq quad32 =
    if p_num_bytes > length p128 * 16 then
      append c128 c_bytes
    else
    c128
  in
  lemma_length_simplifier a128                 a_bytes auth_raw_quads   a_num_bytes;
  lemma_length_simplifier p128 p_bytes plain_raw_quads  p_num_bytes;
  lemma_length_simplifier c128 c_bytes cipher_raw_quads p_num_bytes;
  ()

let decrypt_helper
  (alg:algorithm) (key:seq nat8) (iv:supported_iv_BE) (cipher:seq nat8) (auth:seq nat8)
  (r3:nat64) (alleged_tag_quad computed_tag:quad32) : Lemma
  (requires
    is_aes_key alg key /\    
    length cipher < pow2_32 /\
    length auth < pow2_32 /\
    (if alleged_tag_quad = computed_tag then r3 = 0 else r3 > 0) /\
    be_quad32_to_bytes computed_tag == gcm_decrypt_BE_tag alg key iv cipher auth
  )
  (ensures  (r3 = 0) == snd (gcm_decrypt_BE alg key iv cipher auth (be_quad32_to_bytes alleged_tag_quad)))
  =
  gcm_decrypt_BE_reveal ();
  be_quad32_to_bytes_injective_specific alleged_tag_quad computed_tag;
  ()
