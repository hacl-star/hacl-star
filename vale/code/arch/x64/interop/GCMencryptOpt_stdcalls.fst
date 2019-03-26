module GCMencryptOpt_stdcalls

open Vale.Stdcalls.GCMencryptOpt 
open Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
module V = X64.Vale.Decls
open Gcm_simplify
open GCM_helpers
open FStar.Calc
open FStar.Int.Cast
open FStar.Integers

#reset-options "--lax"

#set-options "--z3rlimit 400 --max_fuel 0 --max_ifuel 0"

let math_aux (n:nat) : Lemma (n * 1 == n) = ()


inline_for_extraction
val gcm128_encrypt_opt':
  key:Ghost.erased (Seq.seq nat32) ->
  auth_b:uint8_p ->
  auth_bytes:uint64 ->
  auth_num:uint64 ->
  keys_b:uint8_p ->
  iv_b:uint8_p ->
  hkeys_b:uint8_p ->
  abytes_b:uint8_p ->
  in128x6_b:uint8_p ->
  out128x6_b:uint8_p ->
  len128x6:uint64 ->
  in128_b:uint8_p ->
  out128_b:uint8_p ->
  len128_num:uint64 ->
  inout_b:uint8_p ->
  plain_num:uint64 ->

  scratch_b:uint8_p ->
  tag_b:uint8_p ->

  Stack unit
    (requires fun h0 ->
      B.disjoint tag_b out128x6_b /\ B.disjoint tag_b out128_b /\
      B.disjoint tag_b inout_b /\ B.disjoint tag_b hkeys_b /\
      disjoint_or_eq tag_b auth_b /\ disjoint_or_eq tag_b iv_b /\
      disjoint_or_eq tag_b keys_b /\ disjoint_or_eq tag_b abytes_b /\
      disjoint_or_eq tag_b in128x6_b /\ disjoint_or_eq tag_b in128_b /\
      disjoint_or_eq tag_b scratch_b /\

      B.disjoint iv_b keys_b /\ B.disjoint iv_b scratch_b /\ B.disjoint iv_b in128x6_b /\
      B.disjoint iv_b out128x6_b /\ B.disjoint iv_b hkeys_b /\ B.disjoint iv_b in128_b /\
      B.disjoint iv_b out128_b /\ B.disjoint iv_b inout_b /\
      disjoint_or_eq iv_b auth_b /\ disjoint_or_eq iv_b abytes_b /\

      B.disjoint scratch_b keys_b /\ B.disjoint scratch_b in128x6_b /\
      B.disjoint scratch_b out128x6_b /\ B.disjoint scratch_b in128_b /\
      B.disjoint scratch_b out128_b /\ B.disjoint scratch_b inout_b /\
      B.disjoint scratch_b hkeys_b /\
      disjoint_or_eq scratch_b auth_b /\ disjoint_or_eq scratch_b abytes_b /\

      B.disjoint out128x6_b keys_b /\ B.disjoint out128x6_b hkeys_b /\
      B.disjoint out128x6_b in128_b /\ B.disjoint out128x6_b inout_b /\
      B.disjoint out128x6_b out128_b /\
      disjoint_or_eq out128x6_b in128x6_b /\
      disjoint_or_eq out128x6_b auth_b /\ disjoint_or_eq out128x6_b abytes_b /\

      B.disjoint out128_b keys_b /\ B.disjoint out128_b hkeys_b /\
      B.disjoint out128_b inout_b /\
      disjoint_or_eq out128_b in128_b /\ disjoint_or_eq out128_b in128x6_b /\
      disjoint_or_eq out128_b auth_b /\ disjoint_or_eq out128_b abytes_b /\

      B.disjoint inout_b keys_b /\ B.disjoint inout_b hkeys_b /\
      disjoint_or_eq inout_b in128_b /\ disjoint_or_eq inout_b in128x6_b /\
      disjoint_or_eq inout_b auth_b /\ disjoint_or_eq inout_b abytes_b /\

      disjoint_or_eq keys_b hkeys_b /\ 
      disjoint_or_eq keys_b in128x6_b /\ disjoint_or_eq keys_b in128_b /\
      disjoint_or_eq keys_b auth_b /\ disjoint_or_eq keys_b abytes_b /\

      disjoint_or_eq hkeys_b in128_b /\ disjoint_or_eq hkeys_b in128x6_b /\
      disjoint_or_eq hkeys_b auth_b /\ disjoint_or_eq hkeys_b abytes_b /\

      disjoint_or_eq in128_b in128x6_b /\ disjoint_or_eq in128_b auth_b /\
      disjoint_or_eq in128_b abytes_b /\
      
      disjoint_or_eq in128x6_b auth_b /\ disjoint_or_eq in128x6_b abytes_b /\
      
      disjoint_or_eq auth_b abytes_b /\

      B.live h0 auth_b /\ B.live h0 abytes_b /\ B.live h0 keys_b /\
      B.live h0 iv_b /\ B.live h0 hkeys_b /\
      B.live h0 in128x6_b /\ B.live h0 out128x6_b /\
      B.live h0 in128_b /\ B.live h0 out128_b /\
      B.live h0 inout_b /\ B.live h0 tag_b /\ B.live h0 scratch_b /\

      B.length auth_b = 16 * UInt64.v auth_num /\
      B.length abytes_b == 16 /\
      B.length iv_b = 16 /\
      B.length in128x6_b == 16 * UInt64.v len128x6 /\
      B.length out128x6_b == B.length in128x6_b /\
      B.length in128_b == 16 * UInt64.v len128_num /\
      B.length out128_b == B.length in128_b /\
      B.length inout_b == 16 /\
      B.length scratch_b == 128 /\
      B.length hkeys_b = 160 /\
      B.length tag_b == 16 /\
      B.length keys_b = 176 /\

      8 * (UInt64.v plain_num) < pow2_32 /\
      4096 * 16 * (UInt64.v len128x6) < pow2_32 /\
      4096 * (UInt64.v len128_num) < pow2_32 /\
      4096 * (UInt64.v auth_bytes) < pow2_32 /\

      UInt64.v len128x6 % 6 == 0 /\
      (UInt64.v len128x6 > 0 ==> UInt64.v len128x6 >= 18) /\
      12 + UInt64.v len128x6 + 6 < pow2_32 /\

      aesni_enabled /\ pclmulqdq_enabled /\
      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    )
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer tag_b)
                  (B.loc_union (B.loc_buffer iv_b)
                  (B.loc_union (B.loc_buffer scratch_b)
                  (B.loc_union (B.loc_buffer out128x6_b)
                  (B.loc_union (B.loc_buffer out128_b)
                  (B.loc_buffer inout_b)))))) h0 h1 /\
      (8 * (UInt64.v plain_num) < pow2_32 /\
       8 * (UInt64.v auth_bytes) < pow2_32 /\ (
       let in128x6_d = get_downview in128x6_b in
       length_aux3 in128x6_b (UInt64.v len128x6);
       let in128x6_u = UV.mk_buffer in128x6_d Views.up_view128 in
       let in128_d = get_downview in128_b in
       length_aux3 in128_b (UInt64.v len128_num);
       let in128_u = UV.mk_buffer in128_d Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;      
       let inout_u = UV.mk_buffer inout_d Views.up_view128 in       
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6);
       let out128x6_u = UV.mk_buffer out128x6_d Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num);
       let out128_u = UV.mk_buffer out128_d Views.up_view128 in       
       length_aux4 iv_b;
       DV.length_eq (get_downview iv_b);
       let iv_LE = low_buffer_read TUInt8 TUInt128 h0 iv_b 0 in
       let iv_BE = reverse_bytes_quad32 iv_LE in
       let ctr_BE_1 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
       let ctr_BE_2 = Mkfour 2 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
       let plain_in =
         if (UInt64.v plain_num > (UInt64.v len128x6 + UInt64.v len128_num) * 128/8) then
           Seq.append (Seq.append (UV.as_seq h0 in128x6_u) (UV.as_seq h0 in128_u))
                      (UV.as_seq h0 inout_u)
         else Seq.append (UV.as_seq h0 in128x6_u) (UV.as_seq h0 in128_u)
       in let cipher_out =
         if (UInt64.v plain_num > (UInt64.v len128x6 + UInt64.v len128_num) * 128/8) then
           Seq.append (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u))
                      (UV.as_seq h1 inout_u)
         else Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u)
       in gctr_partial AES_128 (UInt64.v len128x6 + UInt64.v len128_num + 1) plain_in cipher_out (Ghost.reveal key) ctr_BE_2 /\ (
       DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_num) 0 (8 * UInt64.v auth_bytes) 0) in
       let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_num);
       let auth_u = UV.mk_buffer auth_d Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;      
       let abytes_u = UV.mk_buffer abytes_d Views.up_view128 in        
       let cipher_bytes =
         if UInt64.v plain_num > (UInt64.v len128x6 + UInt64.v len128_num) * 128/8 then
           UV.as_seq h1 inout_u
         else Seq.empty
       in let auth_in =
         if UInt64.v auth_bytes > UInt64.v auth_num * 128 / 8 then
           Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u))
             (UV.as_seq h1 out128x6_u))
             (UV.as_seq h1 out128_u))
             cipher_bytes)
             (Seq.create 1 length_quad)
         else
           Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h1 out128x6_u))
             (UV.as_seq h1 out128_u))
             cipher_bytes)
             (Seq.create 1 length_quad)
       in
       DV.length_eq (get_downview tag_b);
       low_buffer_read TUInt8 TUInt128 h1 tag_b 0 ==
         gctr_encrypt_block ctr_BE_1 (ghash_LE h auth_in) AES_128 (Ghost.reveal key) 0
         )
         ))
    )


inline_for_extraction
let gcm128_encrypt_opt' key auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
  in128x6_b out128x6_b len128x6 in128_b out128_b len128_num inout_b plain_num scratch_b tag_b =
  
  let h0 = get() in

  DV.length_eq (get_downview auth_b);
  DV.length_eq (get_downview keys_b); 
  DV.length_eq (get_downview iv_b);
  DV.length_eq (get_downview hkeys_b); 
  DV.length_eq (get_downview abytes_b);
  DV.length_eq (get_downview in128x6_b);
  DV.length_eq (get_downview out128x6_b);
  DV.length_eq (get_downview in128_b);
  DV.length_eq (get_downview out128_b);
  DV.length_eq (get_downview inout_b);
  DV.length_eq (get_downview scratch_b);
  DV.length_eq (get_downview tag_b);

  math_aux (B.length auth_b);
  math_aux (B.length keys_b);
  math_aux (B.length iv_b);
  math_aux (B.length hkeys_b);
  math_aux (B.length in128x6_b);
  math_aux (B.length scratch_b);
  math_aux (B.length out128_b);
  FStar.Math.Lemmas.cancel_mul_mod (UInt64.v auth_num) 16;
  assert_norm (176 % 16 = 0);
  assert_norm (16 % 16 = 0);
  assert_norm (160 % 16 = 0);
  assert_norm (128 % 16 = 0);
  FStar.Math.Lemmas.cancel_mul_mod (UInt64.v len128x6) 16;
  FStar.Math.Lemmas.cancel_mul_mod (UInt64.v len128_num) 16;

  calc (<=) {
    256 * ((16 * UInt64.v len128_num) / 16);
    (==) {  FStar.Math.Lemmas.cancel_mul_div (UInt64.v len128_num) 16 }
    256 * (UInt64.v len128_num);
    ( <= ) { assert_norm (256 <= 4096); FStar.Math.Lemmas.lemma_mult_le_right (UInt64.v len128_num) 256 4096 }
    4096 * (UInt64.v len128_num);
  };

  assert (DV.length (get_downview tag_b) % 16 = 0);
  assert (DV.length (get_downview scratch_b) % 16 = 0);
  assert (DV.length (get_downview out128_b) % 16 = 0);

  as_vale_buffer_len #TUInt8 #TUInt128 auth_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  as_vale_buffer_len #TUInt8 #TUInt128 iv_b;
  as_vale_buffer_len #TUInt8 #TUInt128 hkeys_b;
  as_vale_buffer_len #TUInt8 #TUInt128 abytes_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out128x6_b;
  as_vale_buffer_len #TUInt8 #TUInt128 in128x6_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out128x6_b;
  as_vale_buffer_len #TUInt8 #TUInt128 in128_b;
  as_vale_buffer_len #TUInt8 #TUInt128 inout_b;
  as_vale_buffer_len #TUInt8 #TUInt128 scratch_b;
  as_vale_buffer_len #TUInt8 #TUInt128 tag_b;
  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 auth_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 in128x6_b);  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out128x6_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 in128_b);  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 out128_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 inout_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 iv_b);  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 keys_b);  
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 hkeys_b);  

  let x, _ = gcm128_encrypt_opt  key auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
  in128x6_b out128x6_b len128x6 in128_b out128_b len128_num inout_b plain_num scratch_b tag_b () in

  let h1 = get() in
  ()


inline_for_extraction
val gcm128_encrypt_opt_alloca:
  key:Ghost.erased (Seq.seq nat32) ->
  plain_b:uint8_p ->
  plain_len:uint64 ->
  auth_b:uint8_p ->
  auth_len:uint64 ->
  iv_b:uint8_p ->
  out_b:uint8_p ->
  tag_b:uint8_p ->
  keys_b:uint8_p ->
  hkeys_b:uint8_p ->

  scratch_b:uint8_p ->
  inout_b : uint8_p ->
  abytes_b : uint8_p ->

  Stack unit
    (requires fun h0 ->
      B.disjoint scratch_b tag_b /\ B.disjoint scratch_b out_b /\
      B.disjoint scratch_b hkeys_b /\ B.disjoint scratch_b plain_b /\
      B.disjoint scratch_b auth_b /\ B.disjoint scratch_b iv_b /\
      B.disjoint scratch_b keys_b /\ B.disjoint scratch_b inout_b /\
      B.disjoint scratch_b abytes_b /\

      B.disjoint inout_b tag_b /\ B.disjoint inout_b out_b /\
      B.disjoint inout_b hkeys_b /\ B.disjoint inout_b plain_b /\
      B.disjoint inout_b auth_b /\ B.disjoint inout_b iv_b /\
      B.disjoint inout_b keys_b /\ B.disjoint inout_b abytes_b /\

      B.disjoint abytes_b tag_b /\ B.disjoint abytes_b out_b /\
      B.disjoint abytes_b hkeys_b /\ B.disjoint abytes_b plain_b /\
      B.disjoint abytes_b auth_b /\ B.disjoint abytes_b iv_b /\
      B.disjoint abytes_b keys_b /\

      B.disjoint tag_b out_b /\ B.disjoint tag_b hkeys_b /\
      B.disjoint tag_b plain_b /\ B.disjoint tag_b auth_b /\
      disjoint_or_eq tag_b iv_b /\ disjoint_or_eq tag_b keys_b /\

      B.disjoint iv_b keys_b /\ B.disjoint iv_b out_b /\
      B.disjoint iv_b plain_b /\ B.disjoint iv_b hkeys_b /\
      B.disjoint iv_b auth_b /\

      B.disjoint out_b keys_b /\ B.disjoint out_b hkeys_b /\
      B.disjoint out_b auth_b /\ disjoint_or_eq out_b plain_b /\
      
      B.disjoint plain_b keys_b /\ B.disjoint plain_b hkeys_b /\
      B.disjoint plain_b auth_b /\

      disjoint_or_eq keys_b hkeys_b /\ 
      B.disjoint keys_b auth_b /\ B.disjoint hkeys_b auth_b /\

      B.live h0 auth_b /\ B.live h0 keys_b /\
      B.live h0 iv_b /\ B.live h0 hkeys_b /\
      B.live h0 out_b /\ B.live h0 plain_b /\
      B.live h0 tag_b /\

      B.live h0 scratch_b /\ B.live h0 inout_b /\ B.live h0 abytes_b /\

      B.length auth_b = (UInt64.v auth_len / 16) * 16 /\
      B.length iv_b = 16 /\
      B.length plain_b = (UInt64.v plain_len / 16) * 16 /\
      B.length out_b = B.length plain_b /\
      B.length hkeys_b = 160 /\
      B.length tag_b == 16 /\
      B.length keys_b = 176 /\

      B.length scratch_b = 128 /\
      B.length inout_b = 16 /\
      B.length abytes_b = 16 /\

      4096 * (UInt64.v plain_len) < pow2_32 /\
      4096 * (UInt64.v auth_len) < pow2_32 /\

      aesni_enabled /\ pclmulqdq_enabled /\
      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    )
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer tag_b)
                  (B.loc_union (B.loc_buffer iv_b)
                  (B.loc_union (B.loc_buffer scratch_b)
                  (B.loc_union (B.loc_buffer out_b)
                  (B.loc_buffer inout_b))))) h0 h1 /\
      (length_aux4 iv_b;
       DV.length_eq (get_downview iv_b);
       let iv_LE = low_buffer_read TUInt8 TUInt128 h0 iv_b 0 in
       let iv_BE = reverse_bytes_quad32 iv_LE in
       let ctr_BE_1 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
       let ctr_BE_2 = Mkfour 2 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
       let plain_d = get_downview plain_b in
       DV.length_eq (get_downview plain_b);
       length_aux3 plain_b (UInt64.v plain_len / 16);       
       let plain_u = UV.mk_buffer plain_d Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;      
       let inout_u = UV.mk_buffer inout_d Views.up_view128 in       
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v plain_len / 16); 
       DV.length_eq (get_downview out_b);
       let out_u = UV.mk_buffer out_d Views.up_view128 in
       let plain_in =
         if (UInt64.v plain_len > B.length plain_b) then
           Seq.append (UV.as_seq h0 plain_u) (UV.as_seq h0 inout_u)
         else UV.as_seq h0 plain_u
       in let cipher_out =
         if (UInt64.v plain_len > B.length plain_b) then
           Seq.append (UV.as_seq h1 out_u)
                      (UV.as_seq h1 inout_u)
         else UV.as_seq h1 out_u in
       
       DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_len) 0 (8 * UInt64.v auth_len) 0) in
       let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_len / 16);
       let auth_u = UV.mk_buffer auth_d Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;      
       let abytes_u = UV.mk_buffer abytes_d Views.up_view128 in        
       let cipher_bytes =
         if UInt64.v plain_len > B.length plain_b then
           UV.as_seq h1 inout_u
         else Seq.empty
       in let auth_in =
         if UInt64.v auth_len > (UInt64.v auth_len / 16) * 128 / 8 then
           Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u))
             (UV.as_seq h1 out_u))
             cipher_bytes)
             (Seq.create 1 length_quad)
         else
           Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h1 out_u))
             cipher_bytes)
             (Seq.create 1 length_quad)
       in
       DV.length_eq (get_downview tag_b);
       low_buffer_read TUInt8 TUInt128 h1 tag_b 0 ==
         gctr_encrypt_block ctr_BE_1 (ghash_LE h auth_in) AES_128 (Ghost.reveal key) 0 /\
       gctr_partial AES_128 (B.length plain_b / 16 + 1) plain_in cipher_out (Ghost.reveal key) ctr_BE_2       
       )
    )

let lemma_same_seq_dv (h:HS.mem) (b:uint8_p) : Lemma
  (Seq.equal (B.as_seq h b) (DV.as_seq h (get_downview b))) =
  let db = get_downview b in
  DV.length_eq db;
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index (B.as_seq h b) i == Seq.index (DV.as_seq h db) i) =
    DV.as_seq_sel h db i;
    DV.get_sel h db i;
    Opaque_s.reveal_opaque Views.put8_def
  in Classical.forall_intro aux

let lemma_uv_split (h:HS.mem) (b:uint8_p) (n:UInt32.t) : Lemma
  (requires B.length b % 16 = 0 /\ UInt32.v n % 16 = 0 /\ UInt32.v n <= B.length b)
  (ensures (
    let b1 = B.gsub b 0ul n in
    let b2 = B.gsub b n (UInt32.uint_to_t (B.length b) - n) in
    let b1_d = get_downview b1 in
    length_aux3 b1 (B.length b1 / 16);
    let b1_u = UV.mk_buffer b1_d Views.up_view128 in
    let b2_d = get_downview b2 in
    length_aux3 b2 (B.length b2 / 16);    
    let b2_u = UV.mk_buffer b2_d Views.up_view128 in
    let b_d = get_downview b in
    length_aux3 b (B.length b / 16);    
    let b_u = UV.mk_buffer b_d Views.up_view128 in       
    let split_bs = Seq.append (UV.as_seq h b1_u) (UV.as_seq h b2_u) in
    let bs = UV.as_seq h b_u in
    Seq.equal bs split_bs)
  ) = 
    let b1 = B.gsub b 0ul n in
    let b2 = B.gsub b n (UInt32.uint_to_t (B.length b) - n) in
    let b1_d = get_downview b1 in
    length_aux3 b1 (B.length b1 / 16);
    let b1_u = UV.mk_buffer b1_d Views.up_view128 in
    let b2_d = get_downview b2 in
    length_aux3 b2 (B.length b2 / 16);    
    let b2_u = UV.mk_buffer b2_d Views.up_view128 in
    let b_d = get_downview b in
    length_aux3 b (B.length b / 16);    
    let b_u = UV.mk_buffer b_d Views.up_view128 in       
    let split_bs = Seq.append (UV.as_seq h b1_u) (UV.as_seq h b2_u) in
    let bs = UV.as_seq h b_u in
    calc (==) {
      Seq.length split_bs;
      (==) { }
      Seq.length (UV.as_seq h b1_u) + Seq.length (UV.as_seq h b2_u);
      (==) { UV.length_eq b1_u; UV.length_eq b2_u }
      DV.length b1_d / 16 + DV.length b2_d / 16;
      (==) { DV.length_eq b1_d; DV.length_eq b2_d; math_aux (B.length b1); math_aux (B.length b2) }
      B.length b1 / 16 + B.length b2 / 16;
      (==) { }
      B.length b / 16;
      (==) { DV.length_eq b_d; UV.length_eq b_u; math_aux (B.length b) }
      Seq.length bs;
    };
    assert (Seq.length bs == Seq.length split_bs);
    let aux (i:nat{ i < Seq.length bs}) : Lemma (Seq.index bs i = Seq.index split_bs i)
      =
        UV.length_eq b_u;
        lemma_same_seq_dv h b;
        calc (==) {
          Seq.index bs i;
          (==) { UV.as_seq_sel h b_u i }
          UV.sel h b_u i;
          (==) { UV.get_sel h b_u i }
          Views.get128 (Seq.slice (DV.as_seq h b_d) (i * 16) (i * 16 + 16));
          (==) { lemma_same_seq_dv h b }
          Views.get128 (Seq.slice (B.as_seq h b) (i * 16) (i * 16 + 16));
          (==) { assert (Seq.equal (B.as_seq h b) (Seq.append (B.as_seq h b1) (B.as_seq h b2))) }
          Views.get128 (Seq.slice (Seq.append (B.as_seq h b1) (B.as_seq h b2)) (i * 16) (i * 16 + 16));
        };
        if i < Seq.length (UV.as_seq h b1_u) then (
          lemma_same_seq_dv h b1;
          UV.length_eq b1_u;
          calc (==) {
            Views.get128 (Seq.slice (Seq.append (B.as_seq h b1) (B.as_seq h b2)) (i * 16) (i * 16 + 16));
            (==) { }
            Views.get128 (Seq.slice (B.as_seq h b1) (i * 16) (i * 16 + 16));
            (==) { UV.get_sel h b1_u i }
            UV.sel h b1_u i;
            (==) { UV.as_seq_sel h b1_u i }
            Seq.index (UV.as_seq h b1_u) i;
            (==) { }
            Seq.index split_bs i;
          }
        ) else (
          lemma_same_seq_dv h b2;
          UV.length_eq b2_u;
          let j = i - UV.length b1_u in
          calc (==) {
            Views.get128 (Seq.slice (Seq.append (B.as_seq h b1) (B.as_seq h b2)) (i * 16) (i * 16 + 16));
            (==) { }
            Views.get128 (Seq.slice (B.as_seq h b2) (j * 16) (j * 16 + 16));
            (==) { UV.get_sel h b2_u j }
            UV.sel h b2_u j;
            (==) { UV.as_seq_sel h b2_u j }
            Seq.index (UV.as_seq h b2_u) j;
            (==) { }
            Seq.index split_bs i;
          }
       )
    in Classical.forall_intro aux

inline_for_extraction
let gcm128_encrypt_opt_alloca key plain_b plain_len auth_b auth_bytes iv_b
  out_b tag_b keys_b hkeys_b scratch_b inout_b abytes_b =

  let h0 = get() in
  
  // Compute length of biggest blocks of 6 * 128-bit blocks
  let len128x6 = UInt64.mul (plain_len / 96uL) 96uL in
  if len128x6 / 16uL >= 18uL then (

    // Compute the size of the remaining 128-bit blocks
    let len128_num = ((plain_len / 16uL) * 16uL) - len128x6 in
    // Casting to uint32 is here the equality
    FStar.Math.Lemmas.small_mod (UInt64.v len128x6) pow2_32;
    FStar.Math.Lemmas.small_mod (UInt64.v len128_num) pow2_32;
    let in128x6_b = B.sub plain_b 0ul (uint64_to_uint32 len128x6) in
    let out128x6_b = B.sub out_b 0ul (uint64_to_uint32 len128x6) in
    calc ( <= ) {
      UInt32.v (uint64_to_uint32 len128x6) + UInt32.v (uint64_to_uint32 len128_num);
      ( == ) { FStar.Math.Lemmas.small_mod (UInt64.v len128x6) pow2_32 }
      UInt64.v len128x6 + UInt32.v (uint64_to_uint32 len128_num);
      ( == ) { FStar.Math.Lemmas.small_mod (UInt64.v len128_num) (pow2 32) }
      UInt64.v len128x6 + UInt64.v len128_num;
      ( == ) { }
      UInt64.v ((plain_len / 16uL) * 16uL);
      ( == ) { }
      ((UInt64.v plain_len) / 16) * 16;
      ( == ) { }
      B.length plain_b;
    };
    let in128_b = B.sub plain_b (uint64_to_uint32 len128x6) (uint64_to_uint32 len128_num) in
    let out128_b = B.sub out_b (uint64_to_uint32 len128x6) (uint64_to_uint32 len128_num) in

    length_aux3 in128x6_b (UInt64.v len128x6 / 16);
    calc ( == ) {
      B.length in128_b;
      (==) { }
      UInt32.v (uint64_to_uint32 len128_num);
      (==) { FStar.Math.Lemmas.small_mod (UInt64.v len128_num) pow2_32 }
      UInt64.v len128_num;
      (==) { FStar.Math.Lemmas.euclidean_division_definition (UInt64.v len128_num) 16 }
      16 * (UInt64.v len128_num / 16);
    };
    length_aux3 in128_b (UInt64.v len128_num / 16);
    length_aux3 out128x6_b (UInt64.v len128x6 / 16);
    length_aux3 out128_b (UInt64.v len128_num / 16);
    length_aux3 inout_b 1;
    length_aux3 plain_b (UInt64.v plain_len / 16);
    length_aux3 out_b (UInt64.v plain_len / 16);

    let auth_num = UInt64.div auth_bytes 16uL in
    let len128x6' = UInt64.div len128x6 16uL in
    let len128_num' = UInt64.div len128_num 16uL in

    calc (==) {
      UInt64.v len128x6' + UInt64.v len128_num';
      (==) { }
      UInt64.v len128x6 / 16 + UInt64.v len128_num / 16;
      (==) { }
      UInt64.v (len128x6 + len128_num) / 16;
      (==) { }
      B.length plain_b / 16;
    };

    calc (==) {
      (UInt64.v len128x6' + UInt64.v len128_num') * 128/8 ;
      (==) { }
      (UInt64.v len128x6 / 16 + UInt64.v len128_num / 16) * 128/8;
      (==) { }
      (UInt64.v (len128x6 + len128_num) / 16) * 128/8;
      (==) { }
      (B.length plain_b / 16) * 128/8;
      (==) { assert_norm (128/8 = 16) }
      (B.length plain_b / 16) * 16;
      (==) { FStar.Math.Lemmas.euclidean_division_definition (B.length plain_b) 16}
      B.length plain_b;
    };

    gcm128_encrypt_opt'
      key
      auth_b 
      auth_bytes
      auth_num
      keys_b 
      iv_b 
      hkeys_b 
      abytes_b 
      in128x6_b
      out128x6_b 
      len128x6'
      in128_b
      out128_b
      len128_num'
      inout_b
      plain_len 
      scratch_b
      tag_b;

    let h1 = get() in

    // Need to prove that seq append commutes…
    assume (
      length_aux4 iv_b;
       DV.length_eq (get_downview iv_b);
       let iv_LE = low_buffer_read TUInt8 TUInt128 h0 iv_b 0 in
       let iv_BE = reverse_bytes_quad32 iv_LE in
       let ctr_BE_1 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in    
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6');
       let out128x6_u = UV.mk_buffer out128x6_d Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num');
       let out128_u = UV.mk_buffer out128_d Views.up_view128 in      
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;      
       let inout_u = UV.mk_buffer inout_d Views.up_view128 in    
      DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_len) 0 (8 * UInt64.v auth_bytes) 0) in
       let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_num);
       let auth_u = UV.mk_buffer auth_d Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;      
       let abytes_u = UV.mk_buffer abytes_d Views.up_view128 in        
       let cipher_bytes =
         if UInt64.v plain_len > (UInt64.v len128x6' + UInt64.v len128_num') * 128/8 then
           UV.as_seq h1 inout_u
         else Seq.empty in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v plain_len / 16); 
       DV.length_eq (get_downview out_b);
       let out_u = UV.mk_buffer out_d Views.up_view128 in         
    Seq.equal
      (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u))
             (UV.as_seq h1 out128x6_u))
             (UV.as_seq h1 out128_u))
             cipher_bytes)
             (Seq.create 1 length_quad))
      (Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u))
             (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u)))
             cipher_bytes)
             (Seq.create 1 length_quad))
          );

    // Need to prove that seq append commutes…
    assume (
      length_aux4 iv_b;
       DV.length_eq (get_downview iv_b);
       let iv_LE = low_buffer_read TUInt8 TUInt128 h0 iv_b 0 in
       let iv_BE = reverse_bytes_quad32 iv_LE in
       let ctr_BE_1 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in    
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6');
       let out128x6_u = UV.mk_buffer out128x6_d Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num');
       let out128_u = UV.mk_buffer out128_d Views.up_view128 in      
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;      
       let inout_u = UV.mk_buffer inout_d Views.up_view128 in    
      DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_len) 0 (8 * UInt64.v auth_bytes) 0) in
       let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_num);
       let auth_u = UV.mk_buffer auth_d Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;      
       let abytes_u = UV.mk_buffer abytes_d Views.up_view128 in        
       let cipher_bytes =
         if UInt64.v plain_len > (UInt64.v len128x6' + UInt64.v len128_num') * 128/8 then
           UV.as_seq h1 inout_u
         else Seq.empty in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v plain_len / 16); 
       DV.length_eq (get_downview out_b);
       let out_u = UV.mk_buffer out_d Views.up_view128 in         
    Seq.equal
      (Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u)
             (UV.as_seq h1 out128x6_u))
             (UV.as_seq h1 out128_u))
             cipher_bytes)
             (Seq.create 1 length_quad))
      (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) 
             (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u)))
             cipher_bytes)
             (Seq.create 1 length_quad))
          );


    lemma_uv_split h0 plain_b (uint64_to_uint32 len128x6);
    let h1 = get() in
    lemma_uv_split h1 out_b (uint64_to_uint32 len128x6)

  ) else (
    admit();
    let len128x6 = 0ul in
    // Compute the size of the remaining 128-bit blocks
    let len128_num = ((plain_len / 16uL) * 16uL) in
    // Casting to uint32 is here the equality
    FStar.Math.Lemmas.small_mod (UInt64.v len128_num) pow2_32;
    let in128x6_b = B.sub plain_b 0ul len128x6 in
    let out128x6_b = B.sub out_b 0ul len128x6 in
    let in128_b = B.sub plain_b len128x6 (uint64_to_uint32 len128_num) in
    let out128_b = B.sub out_b len128x6 (uint64_to_uint32 len128_num) in

    let auth_num = UInt64.div auth_bytes 16uL in
    let len128_num' = UInt64.div len128_num 16uL in
    let len128x6' = 0uL in

    gcm128_encrypt_opt'
      key
      auth_b 
      auth_bytes
      auth_num
      keys_b 
      iv_b 
      hkeys_b 
      abytes_b 
      in128x6_b
      out128x6_b 
      len128x6'
      in128_b
      out128_b
      len128_num'
      inout_b
      plain_len 
      scratch_b
      tag_b;

    let h1 = get() in

   // Need to prove that seq append commutes…
    assume (
      length_aux4 iv_b;
       DV.length_eq (get_downview iv_b);
       let iv_LE = low_buffer_read TUInt8 TUInt128 h0 iv_b 0 in
       let iv_BE = reverse_bytes_quad32 iv_LE in
       let ctr_BE_1 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in    
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6');
       let out128x6_u = UV.mk_buffer out128x6_d Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num');
       let out128_u = UV.mk_buffer out128_d Views.up_view128 in      
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;      
       let inout_u = UV.mk_buffer inout_d Views.up_view128 in    
      DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_len) 0 (8 * UInt64.v auth_bytes) 0) in
       let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_num);
       let auth_u = UV.mk_buffer auth_d Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;      
       let abytes_u = UV.mk_buffer abytes_d Views.up_view128 in        
       let cipher_bytes =
         if UInt64.v plain_len > (UInt64.v len128x6' + UInt64.v len128_num') * 128/8 then
           UV.as_seq h1 inout_u
         else Seq.empty in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v plain_len / 16); 
       DV.length_eq (get_downview out_b);
       let out_u = UV.mk_buffer out_d Views.up_view128 in         
    Seq.equal
      (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u))
             (UV.as_seq h1 out128x6_u))
             (UV.as_seq h1 out128_u))
             cipher_bytes)
             (Seq.create 1 length_quad))
      (Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u))
             (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u)))
             cipher_bytes)
             (Seq.create 1 length_quad))
          );

    // Need to prove that seq append commutes…
    assume (
      length_aux4 iv_b;
       DV.length_eq (get_downview iv_b);
       let iv_LE = low_buffer_read TUInt8 TUInt128 h0 iv_b 0 in
       let iv_BE = reverse_bytes_quad32 iv_LE in
       let ctr_BE_1 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in    
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6');
       let out128x6_u = UV.mk_buffer out128x6_d Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num');
       let out128_u = UV.mk_buffer out128_d Views.up_view128 in      
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;      
       let inout_u = UV.mk_buffer inout_d Views.up_view128 in    
      DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_len) 0 (8 * UInt64.v auth_bytes) 0) in
       let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_num);
       let auth_u = UV.mk_buffer auth_d Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;      
       let abytes_u = UV.mk_buffer abytes_d Views.up_view128 in        
       let cipher_bytes =
         if UInt64.v plain_len > (UInt64.v len128x6' + UInt64.v len128_num') * 128/8 then
           UV.as_seq h1 inout_u
         else Seq.empty in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v plain_len / 16); 
       DV.length_eq (get_downview out_b);
       let out_u = UV.mk_buffer out_d Views.up_view128 in         
    Seq.equal
      (Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u)
             (UV.as_seq h1 out128x6_u))
             (UV.as_seq h1 out128_u))
             cipher_bytes)
             (Seq.create 1 length_quad))
      (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) 
             (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u)))
             cipher_bytes)
             (Seq.create 1 length_quad))
          );

    assume ((UInt64.v len128x6' + UInt64.v len128_num') * 128/8 = B.length plain_b);
    assume (UInt64.v len128x6' + UInt64.v len128_num' = B.length plain_b / 16);

    lemma_uv_split h0 plain_b len128x6;
    
    // Direct postcondition of lemma_uv_split, but needs to be asserted 
    assert (
       let in128x6_d = get_downview in128x6_b in
       length_aux3 in128x6_b (UInt64.v len128x6');
       let in128x6_u = UV.mk_buffer in128x6_d Views.up_view128 in
       let in128_d = get_downview in128_b in
       length_aux3 in128_b (UInt64.v len128_num');
       let in128_u = UV.mk_buffer in128_d Views.up_view128 in 
       let in_d = get_downview plain_b in
       length_aux3 plain_b (B.length plain_b / 16);
       let in_u = UV.mk_buffer in_d Views.up_view128 in 
       let split_bs = Seq.append (UV.as_seq h0 in128x6_u) (UV.as_seq h0 in128_u) in
       let bs = UV.as_seq h0 in_u in
       Seq.equal bs split_bs);

    let h1 = get() in
    lemma_uv_split h1 out_b len128x6;

    // Direct postcondition of lemma_uv_split, but needs to be asserted
    assert (
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6');
       let out128x6_u = UV.mk_buffer out128x6_d Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num');
       let out128_u = UV.mk_buffer out128_d Views.up_view128 in 
       let out_d = get_downview out_b in
       length_aux3 out_b (B.length out_b / 16);
       let out_u = UV.mk_buffer out_d Views.up_view128 in 
       let split_bs = Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u) in
       let bs = UV.as_seq h1 out_u in
       Seq.equal bs split_bs)

  )


inline_for_extraction
val gcm128_encrypt_opt_stdcall':
  key:Ghost.erased (Seq.seq nat32) ->
  plain_b:uint8_p ->
  plain_len:uint64 ->
  auth_b:uint8_p ->
  auth_len:uint64 ->
  iv_b:uint8_p ->
  out_b:uint8_p ->
  tag_b:uint8_p ->
  keys_b:uint8_p ->
  hkeys_b:uint8_p ->

  Stack unit
    (requires fun h0 ->
      B.disjoint tag_b out_b /\ B.disjoint tag_b hkeys_b /\
      B.disjoint tag_b plain_b /\ B.disjoint tag_b auth_b /\
      disjoint_or_eq tag_b iv_b /\ disjoint_or_eq tag_b keys_b /\

      B.disjoint iv_b keys_b /\ B.disjoint iv_b out_b /\
      B.disjoint iv_b plain_b /\ B.disjoint iv_b hkeys_b /\
      B.disjoint iv_b auth_b /\

      B.disjoint out_b keys_b /\ B.disjoint out_b hkeys_b /\
      B.disjoint out_b auth_b /\ disjoint_or_eq out_b plain_b /\
      
      B.disjoint plain_b keys_b /\ B.disjoint plain_b hkeys_b /\
      B.disjoint plain_b auth_b /\

      disjoint_or_eq keys_b hkeys_b /\ 
      B.disjoint keys_b auth_b /\ B.disjoint hkeys_b auth_b /\

      B.live h0 auth_b /\ B.live h0 keys_b /\
      B.live h0 iv_b /\ B.live h0 hkeys_b /\
      B.live h0 out_b /\ B.live h0 plain_b /\
      B.live h0 tag_b /\

      B.length auth_b = UInt64.v auth_len /\
      B.length iv_b = 16 /\
      B.length plain_b = UInt64.v plain_len /\
      B.length out_b = B.length plain_b /\
      B.length hkeys_b = 160 /\
      B.length tag_b == 16 /\
      B.length keys_b = 176 /\

      4096 * (UInt64.v plain_len) < pow2_32 /\
      4096 * (UInt64.v auth_len) < pow2_32 /\

      aesni_enabled /\ pclmulqdq_enabled /\
      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    )
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer tag_b)
                 (B.loc_union (B.loc_buffer iv_b)
                 (B.loc_buffer out_b))) h0 h1 /\

      (length_aux4 iv_b;
       DV.length_eq (get_downview iv_b);
       let iv_LE = low_buffer_read TUInt8 TUInt128 h0 iv_b 0 in
       let iv_BE = reverse_bytes_quad32 iv_LE in
       let ctr_BE_1 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
       let ctr_BE_2 = Mkfour 2 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in

      let plain_in = le_bytes_to_seq_quad32 (pad_to_128_bits (seq_uint8_to_seq_nat8 (B.as_seq h0 plain_b))) in
      let cipher_out = le_bytes_to_seq_quad32 (pad_to_128_bits (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b))) in

       DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_len) 0 (8 * UInt64.v auth_len) 0) in
      let auth_pad = le_bytes_to_seq_quad32 (pad_to_128_bits (seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b))) in
      let auth_in = Seq.append auth_pad (Seq.append cipher_out (Seq.create 1 length_quad)) in

      DV.length_eq (get_downview tag_b);
      low_buffer_read TUInt8 TUInt128 h1 tag_b 0 ==
         gctr_encrypt_block ctr_BE_1 (ghash_LE h auth_in) AES_128 (Ghost.reveal key) 0 /\
       gctr_partial AES_128 (B.length plain_b / 16 + 1) plain_in cipher_out (Ghost.reveal key) ctr_BE_2)
    )

let length_aux6 (b:uint8_p) : Lemma
  (requires B.length b = 16)
  (ensures DV.length (get_downview b) / 16 = 1) =
    let db = get_downview b in
    DV.length_eq db  

let length_aux7 (b:uint8_p) : Lemma
  (requires B.length b = 160)
  (ensures DV.length (get_downview b) / 16 = 10) =
    let db = get_downview b in
    DV.length_eq db  

inline_for_extraction
let gcm128_encrypt_opt_stdcall' key plain_b plain_len auth_b auth_len iv_b out_b tag_b keys_b hkeys_b =
  let h_init = get() in
  let h0 = get() in

  push_frame();
  // Scratch space for Vale procedure
  let scratch_b = B.alloca 0uy 128ul in
  // Extra space to have a full input/output with length % 16 = 0
  let inout_b = B.alloca 0uy 16ul in
  // Same for auth_b
  let abytes_b = B.alloca 0uy 16ul in

  // Copy the remainder of plain_b into inout_b

  FStar.Math.Lemmas.small_mod (UInt64.v plain_len) pow2_32;
  FStar.Math.Lemmas.small_mod (UInt64.v auth_len) pow2_32;

  let plain_len' = (uint64_to_uint32 plain_len / 16ul) * 16ul in
  let auth_len' = (uint64_to_uint32 auth_len / 16ul) * 16ul in
  let plain_b' =  B.sub plain_b 0ul plain_len' in
  let out_b' = B.sub out_b 0ul plain_len' in
  let auth_b' = B.sub auth_b 0ul auth_len' in

  
  B.blit plain_b plain_len' inout_b 0ul (uint64_to_uint32 plain_len % 16ul);

  // Same with auth_b and abytes_b

  B.blit auth_b auth_len' abytes_b 0ul (uint64_to_uint32 auth_len % 16ul);

  let h1 = get() in

  assume (
    let plain_d = get_downview plain_b' in
    DV.length_eq (get_downview plain_b');
    length_aux3 plain_b' (UInt64.v plain_len / 16);
    let plain_u = UV.mk_buffer plain_d Views.up_view128 in
    let inout_d = get_downview inout_b in
    length_aux3 inout_b 1;      
    let inout_u = UV.mk_buffer inout_d Views.up_view128 in       
    let plain_in =
      if (UInt64.v plain_len > UInt32.v plain_len') then
        Seq.append (UV.as_seq h1 plain_u) (UV.as_seq h1 inout_u)
      else UV.as_seq h1 plain_u in
    Seq.equal
      (le_bytes_to_seq_quad32 (pad_to_128_bits (seq_uint8_to_seq_nat8 (B.as_seq h0 plain_b))))
      plain_in
  );

  assume (length_aux6 iv_b;
    length_aux4 iv_b;
    low_buffer_read TUInt8 TUInt128 h0 iv_b 0 == low_buffer_read TUInt8 TUInt128 h1 iv_b 0);

  // Ensures that the view on the keys buffer is the same after allocations
  BufferViewHelpers.lemma_dv_equal Views.down_view8 keys_b h0 h1;
  assert (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (UV.as_seq h1 ub));

  let h0 = get() in

  gcm128_encrypt_opt_alloca
    key
    plain_b'
    plain_len
    auth_b'
    auth_len 
    iv_b
    out_b'
    tag_b
    keys_b 
    hkeys_b 
    scratch_b
    inout_b
    abytes_b;

  let h1 = get() in

  // Copy back the remainder in inout_b into out_b
  B.blit inout_b 0ul out_b ((uint64_to_uint32 plain_len / 16ul) * 16ul) (uint64_to_uint32 plain_len % 16ul);

  let h2 = get() in

  // I don't think this is true right now… We do not have enough information about inout_b to conclude that this is still equivalent to a padding in the end
  assume (
    let out_d = get_downview out_b' in
    length_aux3 out_b' (UInt64.v plain_len / 16); 
    let out_u = UV.mk_buffer out_d Views.up_view128 in
    let inout_d = get_downview inout_b in
    length_aux3 inout_b 1;      
    let inout_u = UV.mk_buffer inout_d Views.up_view128 in       
    let cipher_out =
      if (UInt64.v plain_len > B.length plain_b') then
        Seq.append (UV.as_seq h1 out_u)
                   (UV.as_seq h1 inout_u)
      else UV.as_seq h1 out_u in
    Seq.equal
      (le_bytes_to_seq_quad32 (pad_to_128_bits (seq_uint8_to_seq_nat8 (B.as_seq h2 out_b))))
      cipher_out
  );

  // Same as previous for the same reason
  assume (
    length_aux7 hkeys_b;
    DV.length_eq (get_downview hkeys_b);
    let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
    let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_len) 0 (8 * UInt64.v auth_len) 0) in
    let auth_d = get_downview auth_b' in
    length_aux3 auth_b' (UInt64.v auth_len / 16);
    let auth_u = UV.mk_buffer auth_d Views.up_view128 in
    let abytes_d = get_downview abytes_b in
    length_aux3 abytes_b 1;      
    let abytes_u = UV.mk_buffer abytes_d Views.up_view128 in   
    let out_d = get_downview out_b' in
    length_aux3 out_b' (UInt64.v plain_len / 16); 
    let out_u = UV.mk_buffer out_d Views.up_view128 in
    let inout_d = get_downview inout_b in
    length_aux3 inout_b 1;      
    let inout_u = UV.mk_buffer inout_d Views.up_view128 in       
    let cipher_out =
      if (UInt64.v plain_len > B.length plain_b') then
        Seq.append (UV.as_seq h1 out_u)
                   (UV.as_seq h1 inout_u)
      else UV.as_seq h1 out_u in       
    let cipher_bytes =
         if UInt64.v plain_len > B.length plain_b' then
           UV.as_seq h1 inout_u
         else Seq.empty
    in let auth_in =
         if UInt64.v auth_len > (UInt64.v auth_len / 16) * 128 / 8 then
           Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u))
             (UV.as_seq h1 out_u))
             cipher_bytes)
             (Seq.create 1 length_quad)
         else
           Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h1 out_u))
             cipher_bytes)
             (Seq.create 1 length_quad)

      in
       DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h2 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_len) 0 (8 * UInt64.v auth_len) 0) in
      let auth_pad = le_bytes_to_seq_quad32 (pad_to_128_bits (seq_uint8_to_seq_nat8 (B.as_seq h_init auth_b))) in
      let auth_in2 = Seq.append auth_pad (Seq.append cipher_out (Seq.create 1 length_quad)) in

      Seq.equal auth_in auth_in2
   );

  pop_frame();

  let h_f = get() in

  // Should be derived easily from the fact that the underlying sequences are identical in h1 and h_f
  assume (
    DV.length_eq (get_downview hkeys_b);
    length_aux7 hkeys_b;
    low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0 == low_buffer_read TUInt8 TUInt128 h_f hkeys_b 0);
  assume (
    DV.length_eq (get_downview tag_b);
    length_aux6 tag_b;
    low_buffer_read TUInt8 TUInt128 h1 tag_b 0 == low_buffer_read TUInt8 TUInt128 h_f tag_b 0)

inline_for_extraction
let gcm128_encrypt_opt_stdcall key plain_b plain_len auth_b auth_len iv_b out_b tag_b keys_b hkeys_b =
  let h0 = get() in
  length_aux4 iv_b;
  DV.length_eq (get_downview iv_b);
  Arch.Types.le_bytes_to_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h0 iv_b 0);
  gcm_simplify2 iv_b h0;
  gcm128_encrypt_opt_stdcall' key plain_b plain_len auth_b auth_len iv_b out_b tag_b keys_b hkeys_b
