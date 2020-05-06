module Vale.Wrapper.X64.GCTR

open FStar.Mul
open Vale.Stdcalls.X64.GCTR
open Vale.AsLowStar.MemoryHelpers
open Vale.X64.MemoryAdapters
module V = Vale.X64.Decls
open Vale.SHA.Simplify_Sha
open Vale.AES.Gcm_simplify
open Vale.AES.GCM_helpers
open Vale.Arch.Types

let wrap_slice (#a:Type0) (s:Seq.seq a) (i:int) : Seq.seq a =
  Seq.slice s 0 (if 0 <= i && i <= Seq.length s then i else 0)

let length_aux3 (b:uint8_p) (n:nat) : Lemma
  (requires B.length b = 16 * n)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db;
    FStar.Math.Lemmas.cancel_mul_mod n 16

inline_for_extraction
val gctr128_bytes_stdcall':
  key:Ghost.erased (Seq.seq nat32) ->
  in_b:uint8_p ->
  num_bytes:uint64 ->
  out_b:uint8_p ->
  inout_b: uint8_p ->
  keys_b:uint8_p ->
  ctr_b:uint8_p ->
  num_blocks:uint64 ->
  Stack unit
  (requires fun h0 ->
     B.disjoint in_b out_b /\
     B.disjoint keys_b out_b /\
     (B.disjoint in_b keys_b \/ in_b == keys_b) /\
     B.disjoint ctr_b in_b /\
     B.disjoint ctr_b out_b /\
     B.disjoint ctr_b keys_b /\
     B.disjoint inout_b in_b /\ B.disjoint inout_b out_b /\
     B.disjoint inout_b keys_b /\ B.disjoint inout_b ctr_b /\

     B.live h0 keys_b /\ B.live h0 in_b /\
     B.live h0 out_b /\ B.live h0 ctr_b /\
     B.live h0 inout_b /\

     B.length in_b = 16 * UInt64.v num_blocks /\
     B.length out_b = B.length in_b /\
     B.length ctr_b = 16 /\
     B.length keys_b = Vale.Wrapper.X64.AES.key_offset AES_128 /\
     B.length inout_b = 16 /\

     4096 * (UInt64.v num_blocks) * 16 < pow2_32 /\
     UInt64.v num_blocks * 128/8 <= UInt64.v num_bytes /\
     UInt64.v num_bytes < UInt64.v num_blocks * 128/8 + 128/8 /\

     aesni_enabled /\ avx_enabled /\ sse_enabled /\
     is_aes_key_LE AES_128 (Ghost.reveal key) /\
     (Seq.equal (B.as_seq h0 keys_b)
       (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 (Ghost.reveal key)))))
   )
   (ensures fun h0 r h1 ->
     B.modifies (B.loc_union (B.loc_buffer out_b) (B.loc_buffer inout_b)) h0 h1 /\

     (let ctr = seq_uint8_to_seq_nat8 (B.as_seq h0 ctr_b) in
       let in_d = get_downview in_b in
       length_aux3 in_b (UInt64.v num_blocks);
       let in_u = UV.mk_buffer in_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v num_blocks);
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in

      let plain_quads = Seq.append (UV.as_seq h0 in_u) (UV.as_seq h0 inout_u) in
      let plain = wrap_slice (le_seq_quad32_to_bytes plain_quads) (UInt64.v num_bytes) in
      let cipher_quads = Seq.append (UV.as_seq h1 out_u) (UV.as_seq h1 inout_u) in
      let cipher = wrap_slice (le_seq_quad32_to_bytes cipher_quads) (UInt64.v num_bytes) in
      Seq.equal
        (gctr_encrypt_LE (le_bytes_to_quad32 ctr) (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key))
        cipher
      )
   )

inline_for_extraction
val gctr256_bytes_stdcall':
  key:Ghost.erased (Seq.seq nat32) ->
  in_b:uint8_p ->
  num_bytes:uint64 ->
  out_b:uint8_p ->
  inout_b: uint8_p ->
  keys_b:uint8_p ->
  ctr_b:uint8_p ->
  num_blocks:uint64 ->
  Stack unit
  (requires fun h0 ->
     B.disjoint in_b out_b /\
     B.disjoint keys_b out_b /\
     (B.disjoint in_b keys_b \/ in_b == keys_b) /\
     B.disjoint ctr_b in_b /\
     B.disjoint ctr_b out_b /\
     B.disjoint ctr_b keys_b /\
     B.disjoint inout_b in_b /\ B.disjoint inout_b out_b /\
     B.disjoint inout_b keys_b /\ B.disjoint inout_b ctr_b /\

     B.live h0 keys_b /\ B.live h0 in_b /\
     B.live h0 out_b /\ B.live h0 ctr_b /\
     B.live h0 inout_b /\

     B.length in_b = 16 * UInt64.v num_blocks /\
     B.length out_b = B.length in_b /\
     B.length ctr_b = 16 /\
     B.length keys_b = Vale.Wrapper.X64.AES.key_offset AES_256 /\
     B.length inout_b = 16 /\

     4096 * (UInt64.v num_blocks) * 16 < pow2_32 /\
     UInt64.v num_blocks * 128/8 <= UInt64.v num_bytes /\
     UInt64.v num_bytes < UInt64.v num_blocks * 128/8 + 128/8 /\

     aesni_enabled /\ avx_enabled /\ sse_enabled /\
     is_aes_key_LE AES_256 (Ghost.reveal key) /\
     (Seq.equal (B.as_seq h0 keys_b)
       (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_256 (Ghost.reveal key)))))
   )
   (ensures fun h0 r h1 ->
     B.modifies (B.loc_union (B.loc_buffer out_b) (B.loc_buffer inout_b)) h0 h1 /\

     (let ctr = seq_uint8_to_seq_nat8 (B.as_seq h0 ctr_b) in

       let in_d = get_downview in_b in
       length_aux3 in_b (UInt64.v num_blocks);
       let in_u = UV.mk_buffer in_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out_d = get_downview out_b in
       length_aux3 out_b (UInt64.v num_blocks);
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in

      let plain_quads = Seq.append (UV.as_seq h0 in_u) (UV.as_seq h0 inout_u) in
      let plain = wrap_slice (le_seq_quad32_to_bytes plain_quads) (UInt64.v num_bytes) in
      let cipher_quads = Seq.append (UV.as_seq h1 out_u) (UV.as_seq h1 inout_u) in
      let cipher = wrap_slice (le_seq_quad32_to_bytes cipher_quads) (UInt64.v num_bytes) in
      Seq.equal
        (gctr_encrypt_LE (le_bytes_to_quad32 ctr) (make_gctr_plain_LE plain) AES_256 (Ghost.reveal key))
        cipher
      )
   )

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

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"
inline_for_extraction
let gctr128_bytes_stdcall' key in_b num_bytes out_b inout_b keys_b ctr_b num_blocks =
  let h0 = get() in

  DV.length_eq (get_downview in_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview keys_b);
  DV.length_eq (get_downview ctr_b);
  DV.length_eq (get_downview inout_b);

  as_vale_buffer_len #TUInt8 #TUInt128 in_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  as_vale_buffer_len #TUInt8 #TUInt128 ctr_b;
  as_vale_buffer_len #TUInt8 #TUInt128 inout_b;

  bounded_buffer_addrs_all TUInt8 TUInt128 h0 in_b;
  bounded_buffer_addrs_all TUInt8 TUInt128 h0 keys_b;
  bounded_buffer_addrs_all TUInt8 TUInt128 h0 out_b;

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
  let (x, _) = gctr128_bytes key in_b num_bytes out_b inout_b keys_b ctr_b num_blocks () in

  let h1 = get() in

  // lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 in_b h1;
  // lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 inout_b h0;
  // lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 inout_b h1;
  // lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 out_b h1;
  le_bytes_to_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h0 ctr_b 0);
  gcm_simplify2 ctr_b h0;

  ()

inline_for_extraction
let gctr256_bytes_stdcall' key in_b num_bytes out_b inout_b keys_b ctr_b num_blocks =
  let h0 = get() in

  DV.length_eq (get_downview in_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview inout_b);
  DV.length_eq (get_downview keys_b);
  DV.length_eq (get_downview ctr_b);

  as_vale_buffer_len #TUInt8 #TUInt128 in_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 inout_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  as_vale_buffer_len #TUInt8 #TUInt128 ctr_b;

  bounded_buffer_addrs_all TUInt8 TUInt128 h0 in_b;
  bounded_buffer_addrs_all TUInt8 TUInt128 h0 keys_b;
  bounded_buffer_addrs_all TUInt8 TUInt128 h0 out_b;

  let lemma_uv_key () : Lemma
    (let db = get_downview keys_b in
      length_aux2 keys_b;
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_256 (Ghost.reveal key)))
    = length_aux2 keys_b;
      let db = get_downview keys_b in
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
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
  let (x, _) = gctr256_bytes key in_b num_bytes out_b inout_b keys_b ctr_b num_blocks () in

  let h1 = get() in

  // lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 in_b h1;
  // lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 out_b h1;
  le_bytes_to_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h0 ctr_b 0);
  gcm_simplify2 ctr_b h0;

  ()

let length_aux4 (b:uint8_p) (n:nat) : Lemma
  (requires B.length b = n * 16)
  (ensures DV.length (get_downview b) % 16 = 0) =
  DV.length_eq (get_downview b)

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
    length_aux4 b_start (B.length b / 16);
    let b_start_u = UV.mk_buffer b_start_d Vale.Interop.Views.up_view128 in
    let b_extra_d = get_downview b_extra in
    length_aux4 b_extra 1;
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

open Vale.Lib.BufferViewHelpers

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


let gctr_bytes_stdcall128 key in_b num_bytes out_b keys_b ctr_b =
  push_frame();
  let inout_b = B.alloca 0uy 16ul in


  math_cast_aux num_bytes;
  let num_blocks = (uint64_to_uint32 num_bytes / 16ul) in
  let num_bytes' = num_blocks * 16ul in
  let in_b' = B.sub in_b 0ul num_bytes' in
  let out_b' = B.sub out_b 0ul num_bytes' in

  B.blit in_b num_bytes' inout_b 0ul (uint64_to_uint32 num_bytes % 16ul);

  let h0 = get() in

  let _ = gctr128_bytes_stdcall' key in_b' num_bytes out_b' inout_b keys_b ctr_b (uint32_to_uint64 num_blocks) in

  let h_post = get() in

  assert (let ctr = seq_uint8_to_seq_nat8 (B.as_seq h0 ctr_b) in

       let in_d = get_downview in_b' in
       length_aux3 in_b' (UInt64.v (uint32_to_uint64 num_blocks));
       let in_u = UV.mk_buffer in_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out_d = get_downview out_b' in
       length_aux3 out_b' (UInt64.v (uint32_to_uint64 num_blocks));
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in

      let plain_quads = Seq.append (UV.as_seq h0 in_u) (UV.as_seq h0 inout_u) in
      let plain = wrap_slice (le_seq_quad32_to_bytes plain_quads) (UInt64.v num_bytes) in
      let cipher_quads = Seq.append (UV.as_seq h_post out_u) (UV.as_seq h_post inout_u) in
      let cipher = wrap_slice (le_seq_quad32_to_bytes cipher_quads) (UInt64.v num_bytes) in
      Seq.equal
        (gctr_encrypt_LE (le_bytes_to_quad32 ctr) (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key))
        cipher);


  B.blit inout_b 0ul out_b num_bytes' (uint64_to_uint32 num_bytes % 16ul);

  let h1 = get() in

  lemma_identical_uv out_b' h_post h1;
  lemma_identical_uv inout_b h_post h1;

  lemma_slice_sub out_b out_b' inout_b h1;
  lemma_slice_uv_extra out_b out_b' inout_b h1;

  lemma_slice_sub in_b in_b' inout_b h0;
  lemma_slice_uv_extra in_b in_b' inout_b h0;

  pop_frame()

let gctr_bytes_stdcall256 key in_b num_bytes out_b keys_b ctr_b =
  push_frame();
  let inout_b = B.alloca 0uy 16ul in


  math_cast_aux num_bytes;
  let num_blocks = (uint64_to_uint32 num_bytes / 16ul) in
  let num_bytes' = num_blocks * 16ul in
  let in_b' = B.sub in_b 0ul num_bytes' in
  let out_b' = B.sub out_b 0ul num_bytes' in

  B.blit in_b num_bytes' inout_b 0ul (uint64_to_uint32 num_bytes % 16ul);

  let h0 = get() in

  let _ = gctr256_bytes_stdcall' key in_b' num_bytes out_b' inout_b keys_b ctr_b (uint32_to_uint64 num_blocks) in

  let h_post = get() in

  assert (let ctr = seq_uint8_to_seq_nat8 (B.as_seq h0 ctr_b) in

       let in_d = get_downview in_b' in
       length_aux3 in_b' (UInt64.v (uint32_to_uint64 num_blocks));
       let in_u = UV.mk_buffer in_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let out_d = get_downview out_b' in
       length_aux3 out_b' (UInt64.v (uint32_to_uint64 num_blocks));
       let out_u = UV.mk_buffer out_d Vale.Interop.Views.up_view128 in

      let plain_quads = Seq.append (UV.as_seq h0 in_u) (UV.as_seq h0 inout_u) in
      let plain = wrap_slice (le_seq_quad32_to_bytes plain_quads) (UInt64.v num_bytes) in
      let cipher_quads = Seq.append (UV.as_seq h_post out_u) (UV.as_seq h_post inout_u) in
      let cipher = wrap_slice (le_seq_quad32_to_bytes cipher_quads) (UInt64.v num_bytes) in
      Seq.equal
        (gctr_encrypt_LE (le_bytes_to_quad32 ctr) (make_gctr_plain_LE plain) AES_256 (Ghost.reveal key))
        cipher);


  B.blit inout_b 0ul out_b num_bytes' (uint64_to_uint32 num_bytes % 16ul);

  let h1 = get() in

  lemma_identical_uv out_b' h_post h1;
  lemma_identical_uv inout_b h_post h1;

  lemma_slice_sub out_b out_b' inout_b h1;
  lemma_slice_uv_extra out_b out_b' inout_b h1;

  lemma_slice_sub in_b in_b' inout_b h0;
  lemma_slice_uv_extra in_b in_b' inout_b h0;

  pop_frame()
