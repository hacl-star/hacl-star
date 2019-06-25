module Vale.Wrapper.X64.GCMdecryptOpt

open Vale.Stdcalls.X64.GCMdecryptOpt
open Vale.AsLowStar.MemoryHelpers
open Vale.X64.MemoryAdapters
module V = Vale.X64.Decls
open Vale.SHA.Simplify_Sha
open Vale.AES.Gcm_simplify
open Vale.AES.GCM_helpers
open FStar.Calc
open FStar.Int.Cast
open FStar.Integers
open Vale.Arch.Types
open Vale.Lib.BufferViewHelpers

let wrap_slice (#a:Type0) (s:Seq.seq a) (i:int) : Seq.seq a =
  Seq.slice s 0 (if 0 <= i && i <= Seq.length s then i else 0)

#set-options "--z3rlimit 600 --max_fuel 0 --max_ifuel 0"

let math_aux (n:nat) : Lemma (n * 1 == n) = ()

let length_div (b:uint8_p) : Lemma
  (requires B.length b = 16)
  (ensures DV.length (get_downview b) / 16 = 1)
  = DV.length_eq (get_downview b)

inline_for_extraction
val gcm128_decrypt_opt':
  key:Ghost.erased (Seq.seq nat32) ->
  iv:Ghost.erased supported_iv_LE ->
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
  cipher_num:uint64 ->

  scratch_b:uint8_p ->
  tag_b:uint8_p ->

  Stack UInt64.t
    (requires fun h0 ->
      B.disjoint tag_b out128x6_b /\ B.disjoint tag_b out128_b /\
      B.disjoint tag_b inout_b /\ disjoint_or_eq tag_b hkeys_b /\
      disjoint_or_eq tag_b auth_b /\ B.disjoint tag_b iv_b /\
      disjoint_or_eq tag_b keys_b /\ disjoint_or_eq tag_b abytes_b /\
      disjoint_or_eq tag_b in128x6_b /\ disjoint_or_eq tag_b in128_b /\
      B.disjoint tag_b scratch_b /\

      B.disjoint iv_b keys_b /\ B.disjoint iv_b scratch_b /\ B.disjoint iv_b in128x6_b /\
      B.disjoint iv_b out128x6_b /\ B.disjoint iv_b hkeys_b /\ B.disjoint iv_b in128_b /\
      B.disjoint iv_b out128_b /\ B.disjoint iv_b inout_b /\
      B.disjoint iv_b auth_b /\ B.disjoint iv_b abytes_b /\

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
      B.length scratch_b == 144 /\
      B.length hkeys_b = 128 /\
      B.length tag_b == 16 /\
      B.length keys_b = 176 /\

      UInt64.v cipher_num < pow2_32 /\
      UInt64.v auth_bytes < pow2_32 /\

      UInt64.v len128x6 % 6 == 0 /\
      (UInt64.v len128x6 > 0 ==> UInt64.v len128x6 >= 18) /\
      12 + UInt64.v len128x6 + 6 < pow2_32 /\

      UInt64.v len128x6 * (128/8) + UInt64.v len128_num * (128/8) <= UInt64.v cipher_num /\
      UInt64.v cipher_num < UInt64.v len128x6 * (128/8) + UInt64.v len128_num * (128/8) + 128/8 /\
      UInt64.v auth_num * (128/8) <= UInt64.v auth_bytes /\
      UInt64.v auth_bytes < UInt64.v auth_num * (128/8) + 128/8 /\

      aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled /\
      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key))) /\

      (let db = get_downview hkeys_b in
       length_aux5 hkeys_b;
       let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
       hkeys_reqs_pub (UV.as_seq h0 ub) (reverse_bytes_quad32 (aes_encrypt_LE AES_128 (Ghost.reveal key) (Mkfour 0 0 0 0)))) /\
      (length_div iv_b;
       (reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h0 iv_b 0) ==
         compute_iv_BE (aes_encrypt_LE AES_128 (Ghost.reveal key) (Mkfour 0 0 0 0)) (Ghost.reveal iv))
      )
    
    )
    (ensures fun h0 c h1 ->
      B.modifies  (B.loc_union (B.loc_buffer iv_b)
                  (B.loc_union (B.loc_buffer scratch_b)
                  (B.loc_union (B.loc_buffer out128x6_b)
                  (B.loc_union (B.loc_buffer out128_b)
                  (B.loc_buffer inout_b))))) h0 h1 /\
      (UInt64.v cipher_num < pow2_32 /\
       UInt64.v auth_bytes < pow2_32 /\ (
       let in128x6_d = get_downview in128x6_b in
       length_aux3 in128x6_b (UInt64.v len128x6);
       let in128x6_u = UV.mk_buffer in128x6_d Vale.Interop.Views.up_view128 in
       let in128_d = get_downview in128_b in
       length_aux3 in128_b (UInt64.v len128_num);
       let in128_u = UV.mk_buffer in128_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6);
       let out128x6_u = UV.mk_buffer out128x6_d Vale.Interop.Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num);
       let out128_u = UV.mk_buffer out128_d Vale.Interop.Views.up_view128 in
       let cipher_in =
           Seq.append (Seq.append (UV.as_seq h0 in128x6_u) (UV.as_seq h0 in128_u))
                      (UV.as_seq h0 inout_u)
       in let cipher_bytes = wrap_slice (le_seq_quad32_to_bytes cipher_in) (UInt64.v cipher_num)
       in let plain_out =
           Seq.append (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u))
                      (UV.as_seq h1 inout_u)
       in let plain_bytes = wrap_slice (le_seq_quad32_to_bytes plain_out) (UInt64.v cipher_num)
       in let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_num);
       let auth_u = UV.mk_buffer auth_d Vale.Interop.Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;
       let abytes_u = UV.mk_buffer abytes_d Vale.Interop.Views.up_view128 in
       let auth_in = Seq.append (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u) in
       let auth_bytes = wrap_slice (le_seq_quad32_to_bytes auth_in) (UInt64.v auth_bytes) in
      (length_div tag_b;
       let expected_tag = le_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h0 tag_b 0) in
      Seq.length cipher_bytes < pow2_32 /\
      Seq.length auth_bytes < pow2_32 /\
      is_aes_key AES_128 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) /\
      (let plain, result = gcm_decrypt_LE AES_128 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) (Ghost.reveal iv) cipher_bytes auth_bytes expected_tag in
      Seq.equal plain plain_bytes /\
      (UInt64.v c = 0) == result
      ))))
    )


inline_for_extraction
let gcm128_decrypt_opt' key iv auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
  in128x6_b out128x6_b len128x6 in128_b out128_b len128_num inout_b cipher_num scratch_b tag_b =

  let h0 = get() in
  B.disjoint_neq iv_b auth_b;
  B.disjoint_neq iv_b keys_b;
  B.disjoint_neq iv_b hkeys_b;
  B.disjoint_neq iv_b abytes_b;
  B.disjoint_neq iv_b in128x6_b;
  B.disjoint_neq iv_b out128x6_b;
  B.disjoint_neq iv_b in128_b;
  B.disjoint_neq iv_b out128_b;
  B.disjoint_neq iv_b inout_b;
  B.disjoint_neq iv_b scratch_b;
  B.disjoint_neq iv_b tag_b; 


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
  assert_norm (144 % 16 = 0);
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

  let x, _ = gcm128_decrypt_opt  key iv auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
  in128x6_b out128x6_b len128x6 in128_b out128_b len128_num inout_b cipher_num scratch_b tag_b () in

  let h1 = get() in
  x

inline_for_extraction
val gcm128_decrypt_opt_alloca:
  key:Ghost.erased (Seq.seq nat32) ->
  iv:Ghost.erased supported_iv_LE ->
  cipher_b:uint8_p ->
  cipher_len:uint64 ->
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

  Stack UInt64.t
    (requires fun h0 ->
      B.disjoint scratch_b tag_b /\ B.disjoint scratch_b out_b /\
      B.disjoint scratch_b hkeys_b /\ B.disjoint scratch_b cipher_b /\
      B.disjoint scratch_b auth_b /\ B.disjoint scratch_b iv_b /\
      B.disjoint scratch_b keys_b /\ B.disjoint scratch_b inout_b /\
      B.disjoint scratch_b abytes_b /\

      B.disjoint inout_b tag_b /\ B.disjoint inout_b out_b /\
      B.disjoint inout_b hkeys_b /\ B.disjoint inout_b cipher_b /\
      B.disjoint inout_b auth_b /\ B.disjoint inout_b iv_b /\
      B.disjoint inout_b keys_b /\ B.disjoint inout_b abytes_b /\

      B.disjoint abytes_b tag_b /\ B.disjoint abytes_b out_b /\
      B.disjoint abytes_b hkeys_b /\ B.disjoint abytes_b cipher_b /\
      B.disjoint abytes_b auth_b /\ B.disjoint abytes_b iv_b /\
      B.disjoint abytes_b keys_b /\

      B.disjoint tag_b out_b /\ B.disjoint tag_b hkeys_b /\
      B.disjoint tag_b cipher_b /\ B.disjoint tag_b auth_b /\
      B.disjoint tag_b iv_b /\ disjoint_or_eq tag_b keys_b /\

      B.disjoint iv_b keys_b /\ B.disjoint iv_b out_b /\
      B.disjoint iv_b cipher_b /\ B.disjoint iv_b hkeys_b /\
      B.disjoint iv_b auth_b /\

      B.disjoint out_b keys_b /\ B.disjoint out_b hkeys_b /\
      B.disjoint out_b auth_b /\ disjoint_or_eq out_b cipher_b /\

      B.disjoint cipher_b keys_b /\ B.disjoint cipher_b hkeys_b /\
      B.disjoint cipher_b auth_b /\

      disjoint_or_eq keys_b hkeys_b /\
      B.disjoint keys_b auth_b /\ B.disjoint hkeys_b auth_b /\

      B.live h0 auth_b /\ B.live h0 keys_b /\
      B.live h0 iv_b /\ B.live h0 hkeys_b /\
      B.live h0 out_b /\ B.live h0 cipher_b /\
      B.live h0 tag_b /\

      B.live h0 scratch_b /\ B.live h0 inout_b /\ B.live h0 abytes_b /\

      B.length auth_b = (UInt64.v auth_len / 16) * 16 /\
      B.length iv_b = 16 /\
      B.length cipher_b = (UInt64.v cipher_len / 16) * 16 /\
      B.length out_b = B.length cipher_b /\
      B.length hkeys_b = 128 /\
      B.length tag_b == 16 /\
      B.length keys_b = 176 /\

      B.length scratch_b = 144 /\
      B.length inout_b = 16 /\
      B.length abytes_b = 16 /\

      UInt64.v cipher_len < pow2_32 /\
      UInt64.v auth_len < pow2_32 /\

      aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled /\
      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (Seq.equal (B.as_seq h0 keys_b)
         (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 (Ghost.reveal key))))) /\

      hkeys_reqs_pub (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
        (reverse_bytes_quad32 (aes_encrypt_LE AES_128 (Ghost.reveal key) (Mkfour 0 0 0 0))) /\

      (length_div iv_b;
       (be_bytes_to_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b))) ==
         compute_iv_BE (aes_encrypt_LE AES_128 (Ghost.reveal key) (Mkfour 0 0 0 0)) (Ghost.reveal iv)
      )      
    )
    (ensures fun h0 c h1 ->
      B.modifies  (B.loc_union (B.loc_buffer iv_b)
                  (B.loc_union (B.loc_buffer scratch_b)
                  (B.loc_union (B.loc_buffer out_b)
                  (B.loc_buffer inout_b)))) h0 h1 /\
      (UInt64.v cipher_len) < pow2_32 /\
      (UInt64.v auth_len) < pow2_32 /\
      (let cipher_d = get_downview cipher_b in
       length_aux3 cipher_b (UInt64.v cipher_len / 16);
       let cipher_u = UV.mk_buffer cipher_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v cipher_len / 16);
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in
       let cipher_in = Seq.append (UV.as_seq h0 cipher_u) (UV.as_seq h0 inout_u) in
       let cipher_bytes = wrap_slice (le_seq_quad32_to_bytes cipher_in) (UInt64.v cipher_len) in
       let plain_out = Seq.append (UV.as_seq h1 out_u) (UV.as_seq h1 inout_u) in
       let plain_bytes = wrap_slice (le_seq_quad32_to_bytes plain_out) (UInt64.v cipher_len) in
       let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_len / 16);
       let auth_u = UV.mk_buffer auth_d Vale.Interop.Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;
       let abytes_u = UV.mk_buffer abytes_d Vale.Interop.Views.up_view128 in
       let auth_in = Seq.append (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u) in
       let auth_bytes = wrap_slice (le_seq_quad32_to_bytes auth_in) (UInt64.v auth_len) in
       let expected_tag = seq_uint8_to_seq_nat8 (B.as_seq h0 tag_b) in
      (Seq.length cipher_bytes) < pow2_32 /\
      (Seq.length auth_bytes) < pow2_32 /\
      (let plain, result = gcm_decrypt_LE AES_128 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) (Ghost.reveal iv) cipher_bytes auth_bytes expected_tag in
      Seq.equal plain plain_bytes /\
      (UInt64.v c = 0) == result
      )
    ))

let lemma_same_seq_dv (h:HS.mem) (b:uint8_p) : Lemma
  (Seq.equal (B.as_seq h b) (DV.as_seq h (get_downview b))) =
  let db = get_downview b in
  DV.length_eq db;
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index (B.as_seq h b) i == Seq.index (DV.as_seq h db) i) =
    DV.as_seq_sel h db i;
    DV.get_sel h db i;
    Vale.Def.Opaque_s.reveal_opaque Vale.Interop.Views.put8_def
  in Classical.forall_intro aux

let lemma_uv_split (h:HS.mem) (b:uint8_p) (n:UInt32.t) : Lemma
  (requires B.length b % 16 = 0 /\ UInt32.v n % 16 = 0 /\ UInt32.v n <= B.length b)
  (ensures (
    let b1 = B.gsub b 0ul n in
    let b2 = B.gsub b n (UInt32.uint_to_t (B.length b) - n) in
    let b1_d = get_downview b1 in
    length_aux3 b1 (B.length b1 / 16);
    let b1_u = UV.mk_buffer b1_d Vale.Interop.Views.up_view128 in
    let b2_d = get_downview b2 in
    length_aux3 b2 (B.length b2 / 16);
    let b2_u = UV.mk_buffer b2_d Vale.Interop.Views.up_view128 in
    let b_d = get_downview b in
    length_aux3 b (B.length b / 16);
    let b_u = UV.mk_buffer b_d Vale.Interop.Views.up_view128 in
    let split_bs = Seq.append (UV.as_seq h b1_u) (UV.as_seq h b2_u) in
    let bs = UV.as_seq h b_u in
    Seq.equal bs split_bs)
  ) =
    let b1 = B.gsub b 0ul n in
    let b2 = B.gsub b n (UInt32.uint_to_t (B.length b) - n) in
    let b1_d = get_downview b1 in
    length_aux3 b1 (B.length b1 / 16);
    let b1_u = UV.mk_buffer b1_d Vale.Interop.Views.up_view128 in
    let b2_d = get_downview b2 in
    length_aux3 b2 (B.length b2 / 16);
    let b2_u = UV.mk_buffer b2_d Vale.Interop.Views.up_view128 in
    let b_d = get_downview b in
    length_aux3 b (B.length b / 16);
    let b_u = UV.mk_buffer b_d Vale.Interop.Views.up_view128 in
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
          Vale.Interop.Views.get128 (Seq.slice (DV.as_seq h b_d) (i * 16) (i * 16 + 16));
          (==) { lemma_same_seq_dv h b }
          Vale.Interop.Views.get128 (Seq.slice (B.as_seq h b) (i * 16) (i * 16 + 16));
          (==) { assert (Seq.equal (B.as_seq h b) (Seq.append (B.as_seq h b1) (B.as_seq h b2))) }
          Vale.Interop.Views.get128 (Seq.slice (Seq.append (B.as_seq h b1) (B.as_seq h b2)) (i * 16) (i * 16 + 16));
        };
        if i < Seq.length (UV.as_seq h b1_u) then (
          lemma_same_seq_dv h b1;
          UV.length_eq b1_u;
          calc (==) {
            Vale.Interop.Views.get128 (Seq.slice (Seq.append (B.as_seq h b1) (B.as_seq h b2)) (i * 16) (i * 16 + 16));
            (==) { }
            Vale.Interop.Views.get128 (Seq.slice (B.as_seq h b1) (i * 16) (i * 16 + 16));
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
            Vale.Interop.Views.get128 (Seq.slice (Seq.append (B.as_seq h b1) (B.as_seq h b2)) (i * 16) (i * 16 + 16));
            (==) { }
            Vale.Interop.Views.get128 (Seq.slice (B.as_seq h b2) (j * 16) (j * 16 + 16));
            (==) { UV.get_sel h b2_u j }
            UV.sel h b2_u j;
            (==) { UV.as_seq_sel h b2_u j }
            Seq.index (UV.as_seq h b2_u) j;
            (==) { }
            Seq.index split_bs i;
          }
       )
    in Classical.forall_intro aux

let math_cast_aux (n:UInt64.t) : Lemma
  (requires UInt64.v n < pow2 32)
  (ensures UInt32.v (uint64_to_uint32 n) = UInt64.v n)
  = FStar.Math.Lemmas.small_mod (UInt64.v n) (pow2 32)

inline_for_extraction
let gcm128_decrypt_opt_alloca key iv cipher_b cipher_len auth_b auth_bytes iv_b
  out_b tag_b keys_b hkeys_b scratch_b inout_b abytes_b =

  let h0 = get() in

  let lemma_uv_key () : Lemma
    (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    = length_aux keys_b;
      let db = get_downview keys_b in
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
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

  // Simplify the precondition for hkeys_b
  let lemma_uv_hkey () : Lemma
    (let db = get_downview hkeys_b in
      length_aux5 hkeys_b;
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      UV.as_seq h0 ub == le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
    = length_aux5 hkeys_b;
      let db = get_downview hkeys_b in
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      calc (==) {
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b));
        (==) { lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 hkeys_b h0 }
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (UV.as_seq h0 ub))));
        (==) { le_bytes_to_seq_quad32_to_bytes (UV.as_seq h0 ub) }
        UV.as_seq h0 ub;
      }

  in lemma_uv_hkey ();

  // Simplify the expression for the iv
  DV.length_eq (get_downview iv_b);
  length_aux4 iv_b;
  gcm_simplify3 iv_b h0;

  // Simplify post condition for tag
  gcm_simplify2 tag_b h0;
  length_div tag_b;

  // Compute length of biggest blocks of 6 * 128-bit blocks
  let len128x6 = UInt64.mul (cipher_len / 96uL) 96uL in
  if len128x6 / 16uL >= 18uL then (
    let len128_num = ((cipher_len / 16uL) * 16uL) - len128x6 in
    // Casting to uint32 is here the equality
    math_cast_aux len128x6;
    math_cast_aux len128_num;
    let in128x6_b = B.sub cipher_b 0ul (uint64_to_uint32 len128x6) in
    let out128x6_b = B.sub out_b 0ul (uint64_to_uint32 len128x6) in

    let in128_b = B.sub cipher_b (uint64_to_uint32 len128x6) (uint64_to_uint32 len128_num) in
    let out128_b = B.sub out_b (uint64_to_uint32 len128x6) (uint64_to_uint32 len128_num) in

    let auth_num = UInt64.div auth_bytes 16uL in
    let len128x6' = UInt64.div len128x6 16uL in
    let len128_num' = UInt64.div len128_num 16uL in

    let c = gcm128_decrypt_opt'
      key
      iv
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
      cipher_len
      scratch_b
      tag_b in

    let h1 = get() in
    lemma_uv_split h0 cipher_b (uint64_to_uint32 len128x6);

    // Still need the two asserts for z3 to pick up seq equality
    assert (
       let in128x6_d = get_downview in128x6_b in
       length_aux3 in128x6_b (UInt64.v len128x6');
       let in128x6_u = UV.mk_buffer in128x6_d Vale.Interop.Views.up_view128 in
       let in128_d = get_downview in128_b in
       length_aux3 in128_b (UInt64.v len128_num');
       let in128_u = UV.mk_buffer in128_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let cipher_d = get_downview cipher_b in
       length_aux3 cipher_b (UInt64.v cipher_len / 16);
       let cipher_u = UV.mk_buffer cipher_d Vale.Interop.Views.up_view128 in
       Seq.equal
         (Seq.append (Seq.append (UV.as_seq h0 in128x6_u) (UV.as_seq h0 in128_u))
           (UV.as_seq h0 inout_u))
         (Seq.append (UV.as_seq h0 cipher_u) (UV.as_seq h0 inout_u)));

    lemma_uv_split h1 out_b (uint64_to_uint32 len128x6);

    assert (
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6');
       let out128x6_u = UV.mk_buffer out128x6_d Vale.Interop.Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num');
       let out128_u = UV.mk_buffer out128_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v cipher_len / 16);
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in
       Seq.equal
         (Seq.append (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u))
           (UV.as_seq h1 inout_u))
         (Seq.append (UV.as_seq h1 out_u) (UV.as_seq h1 inout_u)));

    c

  ) else (

    let len128x6 = 0ul in
    // Compute the size of the remaining 128-bit blocks
    let len128_num = ((cipher_len / 16uL) * 16uL) in
    // Casting to uint32 is here the equality
    FStar.Math.Lemmas.small_mod (UInt64.v len128_num) pow2_32;
    let in128x6_b = B.sub cipher_b 0ul len128x6 in
    let out128x6_b = B.sub out_b 0ul len128x6 in
    let in128_b = B.sub cipher_b len128x6 (uint64_to_uint32 len128_num) in
    let out128_b = B.sub out_b len128x6 (uint64_to_uint32 len128_num) in

    let auth_num = UInt64.div auth_bytes 16uL in
    let len128_num' = UInt64.div len128_num 16uL in
    let len128x6' = 0uL in

    let c = gcm128_decrypt_opt'
      key
      iv
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
      cipher_len
      scratch_b
      tag_b in

    let h1 = get() in
    lemma_uv_split h0 cipher_b len128x6;

    // Still need the two asserts for z3 to pick up seq equality
    assert (
       let in128x6_d = get_downview in128x6_b in
       length_aux3 in128x6_b (UInt64.v len128x6');
       let in128x6_u = UV.mk_buffer in128x6_d Vale.Interop.Views.up_view128 in
       let in128_d = get_downview in128_b in
       length_aux3 in128_b (UInt64.v len128_num');
       let in128_u = UV.mk_buffer in128_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let plain_d = get_downview cipher_b in
       length_aux3 cipher_b (UInt64.v cipher_len / 16);
       let plain_u = UV.mk_buffer plain_d Vale.Interop.Views.up_view128 in
       Seq.equal
         (Seq.append (Seq.append (UV.as_seq h0 in128x6_u) (UV.as_seq h0 in128_u))
           (UV.as_seq h0 inout_u))
         (Seq.append (UV.as_seq h0 plain_u) (UV.as_seq h0 inout_u)));

    lemma_uv_split h1 out_b len128x6;

    assert (
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6');
       let out128x6_u = UV.mk_buffer out128x6_d Vale.Interop.Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num');
       let out128_u = UV.mk_buffer out128_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v cipher_len / 16);
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in
       Seq.equal
         (Seq.append (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u))
           (UV.as_seq h1 inout_u))
         (Seq.append (UV.as_seq h1 out_u) (UV.as_seq h1 inout_u)));

    c
  )


let lemma_identical_uv (b:uint8_p) (h0 h1:HS.mem) : Lemma
  (requires B.length b % 16 = 0 /\ Seq.equal (B.as_seq h0 b) (B.as_seq h1 b))
  (ensures (
    let b_d = get_downview b in
    length_aux3 b (B.length b / 16);
    let b_u = UV.mk_buffer b_d Vale.Interop.Views.up_view128 in
    Seq.equal (UV.as_seq h0 b_u) (UV.as_seq h1 b_u)))
  = lemma_dv_equal Vale.Interop.Views.down_view8 b h0 h1;
    length_aux3 b (B.length b / 16);
    lemma_uv_equal Vale.Interop.Views.up_view128 (get_downview b) h0 h1


let length_aux6 (b:uint8_p) : Lemma (B.length b = DV.length (get_downview b))
  = DV.length_eq (get_downview b)

let lemma_slice_uv_extra (b:uint8_p) (b_start:uint8_p) (b_extra:uint8_p) (h:HS.mem) : Lemma
  (requires
    B.length b_start = B.length b / 16 * 16 /\
    b_start == B.gsub b 0ul (UInt32.uint_to_t (B.length b_start)) /\
    B.length b_extra = 16 /\
    Seq.equal
      (B.as_seq h b)
      (Seq.slice (Seq.append (B.as_seq h b_start) (B.as_seq h b_extra)) 0 (B.length b))
    )
  (ensures (
    let b_start_d = get_downview b_start in
    length_aux6 b_start;
    let b_start_u = UV.mk_buffer b_start_d Vale.Interop.Views.up_view128 in
    let b_extra_d = get_downview b_extra in
    length_aux6 b_extra;
    let b_extra_u = UV.mk_buffer b_extra_d Vale.Interop.Views.up_view128 in
    let suv = Seq.append (UV.as_seq h b_start_u) (UV.as_seq h b_extra_u) in
    let sf = wrap_slice (le_seq_quad32_to_bytes suv) (B.length b) in
    Seq.equal sf (seq_uint8_to_seq_nat8 (B.as_seq h b))
 ))
 =
 let b_start_d = get_downview b_start in
 length_aux6 b_start;
 let b_start_u = UV.mk_buffer b_start_d Vale.Interop.Views.up_view128 in
 let b_extra_d = get_downview b_extra in
 length_aux6 b_extra;
 let b_extra_u = UV.mk_buffer b_extra_d Vale.Interop.Views.up_view128 in
 let suv = Seq.append (UV.as_seq h b_start_u) (UV.as_seq h b_extra_u) in
 let sf = wrap_slice (le_seq_quad32_to_bytes suv) (B.length b) in
 let b_f = seq_uint8_to_seq_nat8 (B.as_seq h b) in
 // if B.length b > B.length b_start then (
   calc (==) {
     sf;
     (==) { DV.length_eq b_start_d; lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 b_start h;
          le_bytes_to_seq_quad32_to_bytes (UV.as_seq h b_start_u) }
     wrap_slice (le_seq_quad32_to_bytes (Seq.append
       (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_start)))
       (UV.as_seq h b_extra_u)))
     (B.length b);
     (==) { DV.length_eq b_extra_d; lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 b_extra h;
       le_bytes_to_seq_quad32_to_bytes (UV.as_seq h b_extra_u) }
     wrap_slice (le_seq_quad32_to_bytes (Seq.append
       (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_start)))
       (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_extra)))))
     (B.length b);
     (==) { append_distributes_le_seq_quad32_to_bytes
        (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_start)))
        (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_extra)))
        }
     wrap_slice (Seq.append
       (le_seq_quad32_to_bytes (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_start))))
       (le_seq_quad32_to_bytes (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_extra)))))
     (B.length b);
     (==) { le_seq_quad32_to_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_start));
            le_seq_quad32_to_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h b_extra)) }
     wrap_slice (Seq.append
       (seq_uint8_to_seq_nat8 (B.as_seq h b_start))
       (seq_uint8_to_seq_nat8 (B.as_seq h b_extra)))
     (B.length b);
     (==) { Seq.lemma_eq_intro b_f
       (wrap_slice (Seq.append
         (seq_uint8_to_seq_nat8 (B.as_seq h b_start))
         (seq_uint8_to_seq_nat8 (B.as_seq h b_extra)))
       (B.length b))
     }
     b_f;
   }
 // ) else (
 //   calc (==) {
 //     sf;
 //     (==) { }
 //     wrap_slice (le_seq_quad32_to_bytes (UV.as_seq h b_start_u)) (B.length b);
 //     (==) {    DV.length_eq (get_downview b_start);
 //               gcm_simplify1 b_start h (B.length b) }
 //     seq_uint8_to_seq_nat8 (B.as_seq h b_start);
 //     (==) { }
 //     b_f;
 //   }
 // )

let lemma_slice_sub (b:uint8_p) (b_sub:uint8_p) (b_extra:uint8_p) (h:HS.mem) : Lemma
  (requires B.length b_extra = 16 /\ B.length b_sub = B.length b / 16 * 16 /\
    b_sub == B.gsub b 0ul (UInt32.uint_to_t (B.length b_sub)) /\
    Seq.equal
      (Seq.slice (B.as_seq h b) (B.length b_sub) (B.length b_sub + B.length b % 16))
      (Seq.slice (B.as_seq h b_extra) 0 (B.length b % 16))
  )
  (ensures Seq.equal
    (B.as_seq h b)
    (Seq.slice (Seq.append (B.as_seq h b_sub) (B.as_seq h b_extra)) 0 (B.length b))
  ) =
  calc (==) {
    Seq.slice (Seq.append (B.as_seq h b_sub) (B.as_seq h b_extra)) 0 (B.length b);
    (==) { Seq.lemma_eq_intro
     (Seq.slice (Seq.append (B.as_seq h b_sub) (B.as_seq h b_extra)) 0 (B.length b))
     (Seq.append (B.as_seq h b_sub) (Seq.slice (B.as_seq h b_extra) 0 (B.length b % 16)))
    }
    Seq.append (B.as_seq h b_sub) (Seq.slice (B.as_seq h b_extra) 0 (B.length b % 16));
    (==) { }
    Seq.append
      (Seq.slice (B.as_seq h b) 0 (B.length b_sub))
      (Seq.slice (B.as_seq h b_extra) 0 (B.length b % 16));
    (==) { }
    Seq.append
      (Seq.slice (B.as_seq h b) 0 (B.length b_sub))
      (Seq.slice (B.as_seq h b) (B.length b_sub) (B.length b));
    (==) { Seq.lemma_eq_intro (B.as_seq h b)
      (Seq.append
        (Seq.slice (B.as_seq h b) 0 (B.length b_sub))
        (Seq.slice (B.as_seq h b) (B.length b_sub) (B.length b)))
      }
    B.as_seq h b;
  }

#set-options "--z3rlimit 600 --max_fuel 0 --max_ifuel 0"

inline_for_extraction
let gcm128_decrypt_opt_stdcall key iv cipher_b cipher_len auth_b auth_len iv_b out_b tag_b keys_b hkeys_b scratch_b =
  let h0 = get() in

  push_frame();
  // Extra space to have a full input/output with length % 16 = 0
  let inout_b = B.sub scratch_b 0ul 16ul in
  // Same for auth_b
  let abytes_b = B.sub scratch_b 16ul 16ul in
  // Scratch space for Vale procedure
  let scratch_b = B.sub scratch_b 32ul 144ul in

  // Copy the remainder of cipher_b into inout_b

  math_cast_aux cipher_len;
  math_cast_aux auth_len;

  let cipher_len' = (uint64_to_uint32 cipher_len / 16ul) * 16ul in
  let auth_len' = (uint64_to_uint32 auth_len / 16ul) * 16ul in
  let cipher_b' =  B.sub cipher_b 0ul cipher_len' in
  let out_b' = B.sub out_b 0ul cipher_len' in
  let auth_b' = B.sub auth_b 0ul auth_len' in


  B.blit cipher_b cipher_len' inout_b 0ul (uint64_to_uint32 cipher_len % 16ul);

  let h1 = get() in

  // Same with auth_b and abytes_b

  B.blit auth_b auth_len' abytes_b 0ul (uint64_to_uint32 auth_len % 16ul);

  let h1 = get() in

  let c = gcm128_decrypt_opt_alloca
    key
    iv
    cipher_b'
    cipher_len
    auth_b'
    auth_len
    iv_b
    out_b'
    tag_b
    keys_b
    hkeys_b
    scratch_b
    inout_b
    abytes_b in

  let h_post = get() in

  // Copy back the remainder in inout_b into out_b
  B.blit inout_b 0ul out_b ((uint64_to_uint32 cipher_len / 16ul) * 16ul) (uint64_to_uint32 cipher_len % 16ul);

  let h2 = get() in

  assert (
       let cipher_d = get_downview cipher_b' in
       length_aux3 cipher_b' (UInt64.v cipher_len / 16);
       let cipher_u = UV.mk_buffer cipher_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out_d = get_downview out_b' in
       length_aux3 out_b' (UInt64.v cipher_len / 16);
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in
       let cipher_in = Seq.append (UV.as_seq h1 cipher_u) (UV.as_seq h1 inout_u) in
       let cipher_bytes = wrap_slice (le_seq_quad32_to_bytes cipher_in) (UInt64.v cipher_len) in
       let plain_out = Seq.append (UV.as_seq h_post out_u) (UV.as_seq h_post inout_u) in
       let plain_bytes = wrap_slice (le_seq_quad32_to_bytes plain_out) (UInt64.v cipher_len) in
       let auth_d = get_downview auth_b' in
       length_aux3 auth_b' (UInt64.v auth_len / 16);
       let auth_u = UV.mk_buffer auth_d Vale.Interop.Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;
       let abytes_u = UV.mk_buffer abytes_d Vale.Interop.Views.up_view128 in
       let auth_in = Seq.append (UV.as_seq h1 auth_u) (UV.as_seq h1 abytes_u) in
       let auth_bytes = wrap_slice (le_seq_quad32_to_bytes auth_in) (UInt64.v auth_len) in
       let expected_tag = seq_uint8_to_seq_nat8 (B.as_seq h0 tag_b) in
       (Seq.length cipher_bytes) < pow2_32 /\
       (Seq.length auth_bytes) < pow2_32 /\
       (let plain, result = gcm_decrypt_LE AES_128 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) (Ghost.reveal iv) cipher_bytes auth_bytes expected_tag in
       Seq.equal plain plain_bytes /\
       (UInt64.v c = 0) == result
  ));

  lemma_identical_uv out_b' h_post h2;
  lemma_identical_uv inout_b h_post h2;


  assert (
       let out_d = get_downview out_b' in
       length_aux3 out_b' (UInt64.v cipher_len / 16);
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in
       UV.as_seq h_post out_u == UV.as_seq h2 out_u);

  assert (
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       UV.as_seq h_post inout_u == UV.as_seq h2 inout_u);

  lemma_slice_sub cipher_b cipher_b' inout_b h1;

  lemma_slice_uv_extra cipher_b cipher_b' inout_b h1;

  lemma_slice_sub auth_b auth_b' abytes_b h1;

  lemma_slice_sub out_b out_b' inout_b h2;

  lemma_slice_uv_extra auth_b auth_b' abytes_b h1;
  lemma_slice_uv_extra out_b out_b' inout_b h2;

  assert (
    let cipher = seq_uint8_to_seq_nat8 (B.as_seq h1 cipher_b) in
    let auth = seq_uint8_to_seq_nat8 (B.as_seq h1 auth_b) in
    let expected_tag = seq_uint8_to_seq_nat8 (B.as_seq h1 tag_b) in
    let plain, result = gcm_decrypt_LE AES_128 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) (Ghost.reveal iv) cipher auth expected_tag in
    Seq.equal (seq_uint8_to_seq_nat8 (B.as_seq h2 out_b)) plain /\
    (UInt64.v c = 0) == result);

  pop_frame();
  c
