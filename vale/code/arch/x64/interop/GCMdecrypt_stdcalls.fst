module GCMdecrypt_stdcalls

open Vale.Stdcalls.GCMdecrypt
open Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
module V = X64.Vale.Decls
open Simplify_Sha
open Gcm_simplify
open GCM_helpers
open Workarounds

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

let math_aux (n:nat) : Lemma (n * 1 == n) = ()

inline_for_extraction
val gcm128_decrypt_stdcall':
  key:Ghost.erased (Seq.seq nat32) ->
  cipher_b:uint8_p ->
  cipher_num:uint64 ->
  auth_b:uint8_p ->
  auth_num:uint64 ->
  iv_b:uint8_p ->
  out_b:uint8_p ->
  tag_b:uint8_p ->
  keys_b:uint8_p ->
  Stack UInt64.t 
    (requires fun h0 ->
      B.disjoint cipher_b out_b /\ B.disjoint auth_b out_b /\
      B.disjoint keys_b out_b /\ B.disjoint tag_b out_b /\

      (B.disjoint cipher_b auth_b \/ cipher_b == auth_b) /\
      (B.disjoint cipher_b iv_b \/ cipher_b == iv_b) /\
      (B.disjoint cipher_b tag_b \/ cipher_b == tag_b) /\
      (B.disjoint cipher_b keys_b \/ cipher_b == keys_b) /\
      (B.disjoint auth_b iv_b \/ auth_b == iv_b) /\      
      (B.disjoint auth_b tag_b \/ auth_b == tag_b) /\
      (B.disjoint auth_b keys_b \/ auth_b == keys_b) /\
      (B.disjoint iv_b out_b \/ iv_b == out_b) /\      
      (B.disjoint iv_b tag_b \/ iv_b == tag_b) /\
      (B.disjoint iv_b keys_b \/ iv_b == keys_b) /\     
      (B.disjoint tag_b keys_b \/ tag_b == keys_b) /\     
      
      B.live h0 keys_b /\ B.live h0 cipher_b /\ B.live h0 iv_b /\ 
      B.live h0 out_b /\ B.live h0 tag_b /\ B.live h0 auth_b /\

      B.length cipher_b = 16 * bytes_to_quad_size (UInt64.v cipher_num) /\
      B.length auth_b = 16 * bytes_to_quad_size (UInt64.v auth_num) /\
      B.length iv_b = 16 /\
      B.length out_b = B.length cipher_b /\
      B.length tag_b = 16 /\
      B.length keys_b = 176 /\

      4096 * (UInt64.v cipher_num) < pow2_32 /\
      4096 * (UInt64.v auth_num) < pow2_32 /\
      
      aesni_enabled /\ pclmulqdq_enabled /\
      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (Seq.equal (B.as_seq h0 keys_b)
        (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 (Ghost.reveal key)))))
    )
    (ensures fun h0 r h1 ->
      B.modifies (B.loc_buffer out_b) h0 h1 /\

      (let iv = seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b) in
       let cipher = slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_b)) (UInt64.v cipher_num)  in
       let auth = slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b)) (UInt64.v auth_num)  in
       let tag = seq_uint8_to_seq_nat8 (B.as_seq h0 tag_b) in
       4096 * Seq.length cipher < pow2_32 /\
       4096 * Seq.length auth < pow2_32 /\ (
       let plain, result = gcm_decrypt_LE AES_128 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) iv cipher auth tag in
       Seq.equal plain
         (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) (UInt64.v cipher_num)) /\
       (UInt64.v r = 0) == result))
    )

inline_for_extraction
let gcm128_decrypt_stdcall' key cipher_b cipher_num auth_b auth_num iv_b out_b tag_b keys_b =
  let h0 = get() in
  FStar.Math.Lemmas.lemma_div_mod (bytes_to_quad_size (UInt64.v cipher_num)) 16;
  FStar.Math.Lemmas.lemma_div_mod (bytes_to_quad_size (UInt64.v auth_num)) 16;

  DV.length_eq (get_downview cipher_b);
  DV.length_eq (get_downview auth_b);
  DV.length_eq (get_downview iv_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview tag_b);
  DV.length_eq (get_downview keys_b); 

  math_aux (B.length cipher_b);
  math_aux (B.length auth_b);
  math_aux (B.length iv_b);
  math_aux (B.length keys_b);
  
  as_vale_buffer_len #TUInt8 #TUInt128 cipher_b;
  as_vale_buffer_len #TUInt8 #TUInt128 auth_b;
  as_vale_buffer_len #TUInt8 #TUInt128 iv_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 tag_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 cipher_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 auth_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out_b);

  let lemma_uv_key () : Lemma
    (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    = length_aux keys_b;
      let db = get_downview keys_b in
      let ub = UV.mk_buffer db Views.up_view128 in
      le_bytes_to_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 (Ghost.reveal key));
      assert (Seq.equal (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 keys_b)))
         (key_to_round_keys_LE AES_128 (Ghost.reveal key)));   
      calc (==) {
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 keys_b));
        (==) { lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 keys_b h0 }
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (UV.as_seq h0 ub))));
        (==) { le_bytes_to_seq_quad32_to_bytes (UV.as_seq h0 ub) }
        UV.as_seq h0 ub;
      }

  in lemma_uv_key ();
  let x, _ = gcm128_decrypt key cipher_b cipher_num auth_b auth_num iv_b keys_b out_b tag_b () in

  let h1 = get() in

  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 cipher_b h0;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 auth_b h0;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 out_b h1;  
  gcm_simplify2 tag_b h0;
  gcm_simplify3 iv_b h0;

  x

inline_for_extraction
val gcm256_decrypt_stdcall':
  key:Ghost.erased (Seq.seq nat32) ->
  cipher_b:uint8_p ->
  cipher_num:uint64 ->
  auth_b:uint8_p ->
  auth_num:uint64 ->
  iv_b:uint8_p ->
  out_b:uint8_p ->
  tag_b:uint8_p ->
  keys_b:uint8_p ->
  Stack UInt64.t
    (requires fun h0 ->
      B.disjoint cipher_b out_b /\ B.disjoint auth_b out_b /\
      B.disjoint keys_b out_b /\ B.disjoint tag_b out_b /\

      (B.disjoint cipher_b auth_b \/ cipher_b == auth_b) /\
      (B.disjoint cipher_b iv_b \/ cipher_b == iv_b) /\
      (B.disjoint cipher_b tag_b \/ cipher_b == tag_b) /\
      (B.disjoint cipher_b keys_b \/ cipher_b == keys_b) /\
      (B.disjoint auth_b iv_b \/ auth_b == iv_b) /\      
      (B.disjoint auth_b tag_b \/ auth_b == tag_b) /\
      (B.disjoint auth_b keys_b \/ auth_b == keys_b) /\
      (B.disjoint iv_b out_b \/ iv_b == out_b) /\      
      (B.disjoint iv_b tag_b \/ iv_b == tag_b) /\
      (B.disjoint iv_b keys_b \/ iv_b == keys_b) /\     
      (B.disjoint tag_b keys_b \/ tag_b == keys_b) /\     
      
      B.live h0 keys_b /\ B.live h0 cipher_b /\ B.live h0 iv_b /\ 
      B.live h0 out_b /\ B.live h0 tag_b /\ B.live h0 auth_b /\

      B.length cipher_b = 16 * bytes_to_quad_size (UInt64.v cipher_num) /\
      B.length auth_b = 16 * bytes_to_quad_size (UInt64.v auth_num) /\
      B.length iv_b = 16 /\
      B.length out_b = B.length cipher_b /\
      B.length tag_b = 16 /\
      B.length keys_b = 240 /\

      4096 * (UInt64.v cipher_num) < pow2_32 /\
      4096 * (UInt64.v auth_num) < pow2_32 /\
      
      aesni_enabled /\ pclmulqdq_enabled /\
      is_aes_key_LE AES_256 (Ghost.reveal key) /\
      (Seq.equal (B.as_seq h0 keys_b)
        (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_256 (Ghost.reveal key)))))
    )
    (ensures fun h0 r h1 ->
      B.modifies (B.loc_buffer out_b) h0 h1 /\

      (let iv = seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b) in
       let cipher = slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_b)) (UInt64.v cipher_num)  in
       let auth = slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b)) (UInt64.v auth_num)  in
       let tag = seq_uint8_to_seq_nat8 (B.as_seq h0 tag_b) in
       4096 * Seq.length cipher < pow2_32 /\
       4096 * Seq.length auth < pow2_32 /\ (
       let plain, result = gcm_decrypt_LE AES_256 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) iv cipher auth tag in
       Seq.equal plain
         (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) (UInt64.v cipher_num)) /\
       (UInt64.v r = 0) == result))
    )

inline_for_extraction
let gcm256_decrypt_stdcall' key cipher_b cipher_num auth_b auth_num iv_b out_b tag_b keys_b =
  let h0 = get() in
  FStar.Math.Lemmas.lemma_div_mod (bytes_to_quad_size (UInt64.v cipher_num)) 16;
  FStar.Math.Lemmas.lemma_div_mod (bytes_to_quad_size (UInt64.v auth_num)) 16;

  DV.length_eq (get_downview cipher_b);
  DV.length_eq (get_downview auth_b);
  DV.length_eq (get_downview iv_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview tag_b);
  DV.length_eq (get_downview keys_b); 

  math_aux (B.length cipher_b);
  math_aux (B.length auth_b);
  math_aux (B.length iv_b);
  math_aux (B.length keys_b);

  as_vale_buffer_len #TUInt8 #TUInt128 cipher_b;
  as_vale_buffer_len #TUInt8 #TUInt128 auth_b;
  as_vale_buffer_len #TUInt8 #TUInt128 iv_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 tag_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 cipher_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 auth_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out_b);

  let lemma_uv_key () : Lemma
    (let db = get_downview keys_b in
      length_aux2 keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_256 (Ghost.reveal key)))
    = length_aux2 keys_b;
      let db = get_downview keys_b in
      let ub = UV.mk_buffer db Views.up_view128 in
      le_bytes_to_seq_quad32_to_bytes (key_to_round_keys_LE AES_256 (Ghost.reveal key));
      assert (Seq.equal (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 keys_b)))
         (key_to_round_keys_LE AES_256 (Ghost.reveal key)));   
      calc (==) {
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 keys_b));
        (==) { lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 keys_b h0 }
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (UV.as_seq h0 ub))));
        (==) { le_bytes_to_seq_quad32_to_bytes (UV.as_seq h0 ub) }
        UV.as_seq h0 ub;
      }

  in lemma_uv_key ();
  
  let x, _ = gcm256_decrypt key cipher_b cipher_num auth_b auth_num iv_b keys_b out_b tag_b () in

  let h1 = get() in

  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 cipher_b h0;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 auth_b h0;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 out_b h1;  
  gcm_simplify2 tag_b h0;
  gcm_simplify3 iv_b h0;

  x

open FStar.Integers
open FStar.Int.Cast

let math_cast_aux (n:UInt64.t) : Lemma
  (requires UInt64.v n < pow2 32)
  (ensures UInt32.v (uint64_to_uint32 n) = UInt64.v n)
  = FStar.Math.Lemmas.small_mod (UInt64.v n) (pow2 32)

inline_for_extraction
let bytes_to_quad_size_st (l:UInt32.t{4096 * UInt32.v l < pow2_32}) : Tot 
  (n:UInt32.t{UInt32.v n == 16 * bytes_to_quad_size (UInt32.v l)})
  = 
  assert (UInt32.v l - 15 < pow2_32);
  FStar.Math.Lemmas.euclidean_division_definition (UInt32.v l + 15) 16;
  assert (16 * ((UInt32.v l + 15) / 16) < pow2_32);
  16ul * ((l + 15ul) / 16ul)

inline_for_extraction
let gcm128_decrypt_stdcall key cipher_b cipher_len auth_b auth_len iv_b out_b tag_b keys_b =
  push_frame();

  math_cast_aux auth_len;
  math_cast_aux cipher_len;
  let cipher_len' = uint64_to_uint32 cipher_len in
  let auth_len' = uint64_to_uint32 auth_len in

  let cipher_extlength = bytes_to_quad_size_st cipher_len' in
  let auth_extlength = bytes_to_quad_size_st auth_len' in

  // Allocate buffers that 'extend' initial buffers
  // Dirty hack: The length could be 0 and we cannot allocate a buffer of size 0.
  let cipher_extra = B.alloca 0uy (cipher_extlength + 1ul) in
  let out_extra = B.alloca 0uy (cipher_extlength + 1ul) in
  let auth_extra = B.alloca 0uy (auth_extlength + 1ul) in

  let cipher_extra = B.sub cipher_extra 0ul cipher_extlength in
  let out_extra = B.sub out_extra 0ul cipher_extlength in
  let auth_extra = B.sub auth_extra 0ul auth_extlength in  

  // Copy the initial contents in these buffers
  B.blit cipher_b 0ul cipher_extra 0ul cipher_len';
  B.blit auth_b 0ul auth_extra 0ul auth_len';

  let h0 = get() in
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_extra)) (UInt64.v cipher_len))
    (seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_b)));
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 auth_extra)) (UInt64.v auth_len))
    (seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b)));

  let x = gcm128_decrypt_stdcall' key cipher_extra cipher_len auth_extra auth_len iv_b out_extra tag_b keys_b in

  B.blit out_extra 0ul out_b 0ul cipher_len';

  let h1 = get() in
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h1 out_extra)) (UInt64.v cipher_len))
    (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)));

  assert (let iv = seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b) in
       let cipher = seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_b) in
       let auth = seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b) in
       let tag = seq_uint8_to_seq_nat8 (B.as_seq h0 tag_b) in
       let plain, result = gcm_decrypt_LE AES_128 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) iv cipher auth tag in
       Seq.equal (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) plain);

  pop_frame();

  x
  
inline_for_extraction
let gcm256_decrypt_stdcall key cipher_b cipher_len auth_b auth_len iv_b out_b tag_b keys_b =
  push_frame();

  math_cast_aux auth_len;
  math_cast_aux cipher_len;
  let cipher_len' = uint64_to_uint32 cipher_len in
  let auth_len' = uint64_to_uint32 auth_len in

  let cipher_extlength = bytes_to_quad_size_st cipher_len' in
  let auth_extlength = bytes_to_quad_size_st auth_len' in

  // Allocate buffers that 'extend' initial buffers
  // Dirty hack: The length could be 0 and we cannot allocate a buffer of size 0.
  let cipher_extra = B.alloca 0uy (cipher_extlength + 1ul) in
  let out_extra = B.alloca 0uy (cipher_extlength + 1ul) in
  let auth_extra = B.alloca 0uy (auth_extlength + 1ul) in

  let cipher_extra = B.sub cipher_extra 0ul cipher_extlength in
  let out_extra = B.sub out_extra 0ul cipher_extlength in
  let auth_extra = B.sub auth_extra 0ul auth_extlength in  

  // Copy the initial contents in these buffers
  B.blit cipher_b 0ul cipher_extra 0ul cipher_len';
  B.blit auth_b 0ul auth_extra 0ul auth_len';

  let h0 = get() in
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_extra)) (UInt64.v cipher_len))
    (seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_b)));
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 auth_extra)) (UInt64.v auth_len))
    (seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b)));

  let x = gcm256_decrypt_stdcall' key cipher_extra cipher_len auth_extra auth_len iv_b out_extra tag_b keys_b in

  B.blit out_extra 0ul out_b 0ul cipher_len';

  let h1 = get() in
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h1 out_extra)) (UInt64.v cipher_len))
    (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)));

  assert (let iv = seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b) in
       let cipher = seq_uint8_to_seq_nat8 (B.as_seq h0 cipher_b) in
       let auth = seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b) in
       let tag = seq_uint8_to_seq_nat8 (B.as_seq h0 tag_b) in
       let plain, result = gcm_decrypt_LE AES_256 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) iv cipher auth tag in
       Seq.equal (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) plain);

  pop_frame();

  x
