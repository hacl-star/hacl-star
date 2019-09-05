module Vale.Wrapper.X64.GCM_IV

open FStar.Mul
open Vale.Stdcalls.X64.GCM_IV
open Vale.AsLowStar.MemoryHelpers
open Vale.X64.MemoryAdapters
module V = Vale.X64.Decls
open Vale.SHA.Simplify_Sha
open Vale.AES.Gcm_simplify
open Vale.AES.GCM_helpers
open Vale.Arch.Types
open Vale.AES.GHash
open FStar.Integers
open FStar.Int.Cast

let wrap_slice (#a:Type0) (s:Seq.seq a) (i:int) : Seq.seq a =
  Seq.slice s 0 (if 0 <= i && i <= Seq.length s then i else 0)

let length_aux (b:uint8_p) (n:nat) : Lemma
  (requires B.length b = 16 * n)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db;
    FStar.Math.Lemmas.cancel_mul_mod n 16

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let length_aux5 (b:uint8_p) : Lemma
  (requires B.length b = 128)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db


#push-options "--z3cliopt smt.arith.nl=true"
inline_for_extraction
val compute_iv_stdcall':
  iv:Ghost.erased supported_iv_LE ->
  iv_b:uint8_p ->
  num_bytes:uint64 ->
  len:uint64 ->
  j0_b:uint8_p ->
  iv_extra_b:uint8_p ->
  hkeys_b:uint8_p ->
  Stack unit
  (requires fun h0 ->
    B.disjoint iv_b j0_b /\ B.disjoint iv_b iv_extra_b /\ B.disjoint iv_b hkeys_b /\
    (B.disjoint j0_b iv_extra_b \/ j0_b == iv_extra_b) /\
    B.disjoint j0_b hkeys_b /\ B.disjoint iv_extra_b hkeys_b /\

    B.live h0 iv_b /\ B.live h0 j0_b /\ B.live h0 iv_extra_b /\ B.live h0 hkeys_b /\

    B.length iv_b == 16 * UInt64.v len /\
    B.length j0_b == 16 /\
    B.length iv_extra_b == 16 /\
    B.length hkeys_b == 128 /\

    UInt64.v len * (128/8) <= UInt64.v num_bytes /\
    UInt64.v num_bytes < UInt64.v len * (128/8) + 128/8 /\

    0 < 8 * UInt64.v num_bytes /\
    8 * UInt64.v num_bytes < pow2_64 /\

    pclmulqdq_enabled /\ avx_enabled /\

    (  let db = get_downview hkeys_b in
       length_aux5 hkeys_b; DV.length_eq (get_downview hkeys_b);
       let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
       hkeys_reqs_pub (UV.as_seq h0 ub) (reverse_bytes_quad32
         (reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h0 hkeys_b 2)))) /\


    (  let in_d = get_downview iv_b in
       length_aux iv_b (UInt64.v len);
       let in_u = UV.mk_buffer in_d Vale.Interop.Views.up_view128 in
       let inout_d = get_downview iv_extra_b in
       length_aux iv_extra_b 1;
       let inout_u = UV.mk_buffer inout_d Vale.Interop.Views.up_view128 in
       let iv_raw_quads = Seq.append (UV.as_seq h0 in_u) (UV.as_seq h0 inout_u) in
       let iv_bytes_LE = wrap_slice (le_seq_quad32_to_bytes iv_raw_quads) (UInt64.v num_bytes) in
       Seq.equal iv_bytes_LE (Ghost.reveal iv)
    )
    )
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer j0_b) h0 h1 /\
    (DV.length_eq (get_downview hkeys_b); DV.length_eq (get_downview j0_b);
    let h_LE = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h0 hkeys_b 2) in
    low_buffer_read TUInt8 TUInt128 h1 j0_b 0 == compute_iv_BE h_LE (Ghost.reveal iv))
   )
#pop-options

#push-options "--z3cliopt smt.arith.nl=true"
inline_for_extraction
let compute_iv_stdcall' iv iv_b num_bytes len j0_b iv_extra_b hkeys_b =
  let h0 = get() in

  DV.length_eq (get_downview iv_b);
  DV.length_eq (get_downview iv_extra_b);
  DV.length_eq (get_downview j0_b);
  DV.length_eq (get_downview hkeys_b);

  as_vale_buffer_len #TUInt8 #TUInt128 iv_b;
  as_vale_buffer_len #TUInt8 #TUInt128 iv_extra_b;
  as_vale_buffer_len #TUInt8 #TUInt128 j0_b;
  as_vale_buffer_len #TUInt8 #TUInt128 hkeys_b;

  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 iv_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 hkeys_b);

  let x, _ = compute_iv_stdcall iv iv_b num_bytes len j0_b iv_extra_b hkeys_b () in

  ()
#pop-options

#push-options "--z3cliopt smt.arith.nl=true"
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
    DV.length_eq (get_downview b_start);
    let b_start_u = UV.mk_buffer b_start_d Vale.Interop.Views.up_view128 in
    let b_extra_d = get_downview b_extra in
    DV.length_eq (get_downview b_extra);
    let b_extra_u = UV.mk_buffer b_extra_d Vale.Interop.Views.up_view128 in
    let suv = Seq.append (UV.as_seq h b_start_u) (UV.as_seq h b_extra_u) in
    let sf = wrap_slice (le_seq_quad32_to_bytes suv) (B.length b) in
    Seq.equal sf (seq_uint8_to_seq_nat8 (B.as_seq h b))
 ))
 =
 let b_start_d = get_downview b_start in
 DV.length_eq (get_downview b_start);
 let b_start_u = UV.mk_buffer b_start_d Vale.Interop.Views.up_view128 in
 let b_extra_d = get_downview b_extra in
 DV.length_eq (get_downview b_extra);
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
#pop-options

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


#push-options "--smtencoding.nl_arith_repr boxwrap"
let lemma_same_seq_same_buffer_read (h0 h1:HS.mem) (b:uint8_p) : Lemma
    (requires
      B.live h0 b /\ B.live h1 b /\
      B.length b == 128 /\ B.as_seq h0 b `Seq.equal` B.as_seq h1 b)
   (ensures (
     DV.length_eq (get_downview b);
     low_buffer_read TUInt8 TUInt128 h0 b 2 == low_buffer_read TUInt8 TUInt128 h1 b 2)
   )
   =
   let b_d = get_downview b in
   DV.length_eq b_d;
   let b_u = UV.mk_buffer b_d Vale.Interop.Views.up_view128 in
   lemma_dv_equal Vale.Interop.Views.down_view8 b h0 h1;
   lemma_uv_equal Vale.Interop.Views.up_view128 (get_downview b) h0 h1;
   UV.length_eq b_u;
   UV.as_seq_sel h0 b_u 2;
   UV.as_seq_sel h1 b_u 2
#pop-options

inline_for_extraction
let compute_iv a key full_iv_b num_bytes j0_b extra_b hkeys_b =
  let h0 = get() in
  let len = num_bytes / 16ul in
  let bytes_len = len * 16ul in
  let iv_b = B.sub full_iv_b 0ul bytes_len in

  B.blit full_iv_b bytes_len extra_b 0ul (num_bytes % 16ul);

  let h1 = get() in
  lemma_slice_sub full_iv_b iv_b extra_b h1;
  lemma_slice_uv_extra full_iv_b iv_b extra_b h1;


  DV.length_eq (get_downview hkeys_b); DV.length_eq (get_downview j0_b);

  lemma_same_seq_same_buffer_read h0 h1 hkeys_b;

  let aux () : Lemma
    (aes_encrypt_LE a (Ghost.reveal key) (Mkfour 0 0 0 0) ==
      reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h0 hkeys_b 2))
  = let keys_quad = le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)) in
    let h_BE = low_buffer_read TUInt8 TUInt128 h0 hkeys_b 2 in
    lemma_hkeys_reqs_pub_priv
       keys_quad
       (reverse_bytes_quad32 (aes_encrypt_LE a (Ghost.reveal key) (Mkfour 0 0 0 0)));

    let db = get_downview hkeys_b in
    let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in

    calc (==) {
      le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b));
      (==) { lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 hkeys_b h0 }
      le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (UV.as_seq h0 ub))));
      (==) { le_bytes_to_seq_quad32_to_bytes (UV.as_seq h0 ub) }
      UV.as_seq h0 ub;
    };

      UV.as_seq_sel h0 ub 2;
      reveal_reverse_bytes_quad32 h_BE;
      reveal_reverse_bytes_quad32 (reverse_bytes_quad32 h_BE)

  in aux();


  let lemma_uv_key () : Lemma
    (let db = get_downview hkeys_b in
      length_aux5 hkeys_b;
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      Seq.length (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b))) == 8 /\
      Seq.equal (UV.as_seq h1 ub) (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b))))
    = length_aux5 hkeys_b;
      let db = get_downview hkeys_b in
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      DV.length_eq db;
      UV.length_eq ub;
      calc (==) {
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b));
        (==) { lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 hkeys_b h1 }
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (UV.as_seq h1 ub))));
        (==) { le_bytes_to_seq_quad32_to_bytes (UV.as_seq h1 ub) }
        UV.as_seq h1 ub;
      }

  in lemma_uv_key ();

  compute_iv_stdcall' (Ghost.hide (seq_uint8_to_seq_nat8 (B.as_seq h0 full_iv_b)))
    iv_b (uint32_to_uint64 num_bytes) (uint32_to_uint64 len)
     j0_b  extra_b hkeys_b;
  let h2 = get() in


  gcm_simplify2 j0_b h2;

  le_bytes_to_quad32_to_bytes (compute_iv_BE (aes_encrypt_LE a (Ghost.reveal key) (Mkfour 0 0 0 0))
    (seq_uint8_to_seq_nat8 (B.as_seq h0 full_iv_b)))
