module GCTR_stdcalls

open Vale.Stdcalls.GCTR
open Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
module V = X64.Vale.Decls
open Simplify_Sha
open Gcm_simplify
open GCM_helpers
open Workarounds
open Arch.Types

inline_for_extraction
val gctr128_bytes_stdcall':
  key:Ghost.erased (Seq.seq nat32) ->
  in_b:uint8_p ->
  num_bytes:uint64 ->
  out_b:uint8_p ->
  keys_b:uint8_p ->
  ctr_b:uint8_p ->
  Stack unit
  (requires fun h0 ->
     B.disjoint in_b out_b /\
     B.disjoint keys_b out_b /\
     (B.disjoint in_b keys_b \/ in_b == keys_b) /\
     B.disjoint ctr_b in_b /\
     B.disjoint ctr_b out_b /\
     B.disjoint ctr_b keys_b /\

     B.live h0 keys_b /\ B.live h0 in_b /\
     B.live h0 out_b /\ B.live h0 ctr_b /\

     B.length in_b = 16 * bytes_to_quad_size (UInt64.v num_bytes) /\
     B.length out_b = B.length in_b /\
     B.length ctr_b = 16 /\
     B.length keys_b = AES_stdcalls.key_offset AES_128 /\

     4096 * (UInt64.v num_bytes) < pow2_32 /\

     aesni_enabled /\
     is_aes_key_LE AES_128 (Ghost.reveal key) /\
     (Seq.equal (B.as_seq h0 keys_b)
       (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 (Ghost.reveal key)))))
   )
   (ensures fun h0 r h1 ->
     B.modifies (B.loc_buffer out_b) h0 h1 /\

     (let ctr = seq_uint8_to_seq_nat8 (B.as_seq h0 ctr_b) in
      let plain = slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 in_b)) (UInt64.v num_bytes) in
      let cipher = slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) (UInt64.v num_bytes) in
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
  keys_b:uint8_p ->
  ctr_b:uint8_p ->
  Stack unit
  (requires fun h0 ->
     B.disjoint in_b out_b /\
     B.disjoint keys_b out_b /\
     (B.disjoint in_b keys_b \/ in_b == keys_b) /\
     B.disjoint ctr_b in_b /\
     B.disjoint ctr_b out_b /\
     B.disjoint ctr_b keys_b /\

     B.live h0 keys_b /\ B.live h0 in_b /\
     B.live h0 out_b /\ B.live h0 ctr_b /\

     B.length in_b = 16 * bytes_to_quad_size (UInt64.v num_bytes) /\
     B.length out_b = B.length in_b /\
     B.length ctr_b = 16 /\
     B.length keys_b = AES_stdcalls.key_offset AES_256 /\

     4096 * (UInt64.v num_bytes) < pow2_32 /\

     aesni_enabled /\
     is_aes_key_LE AES_256 (Ghost.reveal key) /\
     (Seq.equal (B.as_seq h0 keys_b)
       (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_256 (Ghost.reveal key)))))
   )
   (ensures fun h0 r h1 ->
     B.modifies (B.loc_buffer out_b) h0 h1 /\

     (let ctr = seq_uint8_to_seq_nat8 (B.as_seq h0 ctr_b) in
      let plain = slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 in_b)) (UInt64.v num_bytes) in
      let cipher = slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) (UInt64.v num_bytes) in
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
let gctr128_bytes_stdcall' key in_b num_bytes out_b keys_b ctr_b =
  let h0 = get() in
  FStar.Math.Lemmas.lemma_div_mod (bytes_to_quad_size (UInt64.v num_bytes)) 16;

  DV.length_eq (get_downview in_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview keys_b);
  DV.length_eq (get_downview ctr_b);

  as_vale_buffer_len #TUInt8 #TUInt128 in_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  as_vale_buffer_len #TUInt8 #TUInt128 ctr_b;

  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 in_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 keys_b);
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
  let x, _ = gctr128_bytes key in_b num_bytes out_b keys_b ctr_b () in

  let h1 = get() in

  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 in_b h1;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 out_b h1; 
  le_bytes_to_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h0 ctr_b 0);
  gcm_simplify2 ctr_b h0;

  ()

inline_for_extraction
let gctr256_bytes_stdcall' key in_b num_bytes out_b keys_b ctr_b =
  let h0 = get() in
  FStar.Math.Lemmas.lemma_div_mod (bytes_to_quad_size (UInt64.v num_bytes)) 16;

  DV.length_eq (get_downview in_b);
  DV.length_eq (get_downview out_b);
  DV.length_eq (get_downview keys_b);
  DV.length_eq (get_downview ctr_b);

  as_vale_buffer_len #TUInt8 #TUInt128 in_b;
  as_vale_buffer_len #TUInt8 #TUInt128 out_b;
  as_vale_buffer_len #TUInt8 #TUInt128 keys_b;
  as_vale_buffer_len #TUInt8 #TUInt128 ctr_b;

  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 in_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 keys_b);
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
  let x, _ = gctr256_bytes key in_b num_bytes out_b keys_b ctr_b () in

  let h1 = get() in

  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 in_b h1;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 out_b h1; 
  le_bytes_to_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h0 ctr_b 0);
  gcm_simplify2 ctr_b h0;

  ()


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

  math_cast_aux num_bytes;
  let num_bytes' = uint64_to_uint32 num_bytes in

  let in_extlength = bytes_to_quad_size_st num_bytes' in

  // Allocate buffers that 'extend' initial buffers
  // Dirty hack: The length could be 0 and we cannot allocate a buffer of size 0.
  let in_extra = B.alloca 0uy (in_extlength + 1ul) in
  let out_extra = B.alloca 0uy (in_extlength + 1ul) in

  let in_extra = B.sub in_extra 0ul in_extlength in
  let out_extra = B.sub out_extra 0ul in_extlength in

  // Copy the initial contents in these buffers
  B.blit in_b 0ul in_extra 0ul num_bytes';

  let h0 = get() in
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 in_extra)) (UInt64.v num_bytes))
    (seq_uint8_to_seq_nat8 (B.as_seq h0 in_b)));

  let _ = gctr128_bytes_stdcall' key in_extra num_bytes out_extra keys_b ctr_b in

  B.blit out_extra 0ul out_b 0ul num_bytes';

  let h1 = get() in
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h1 out_extra)) (UInt64.v num_bytes))
    (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)));

  pop_frame()


let gctr_bytes_stdcall256 key in_b num_bytes out_b keys_b ctr_b =
  push_frame();

  math_cast_aux num_bytes;
  let num_bytes' = uint64_to_uint32 num_bytes in

  let in_extlength = bytes_to_quad_size_st num_bytes' in

  // Allocate buffers that 'extend' initial buffers
  // Dirty hack: The length could be 0 and we cannot allocate a buffer of size 0.
  let in_extra = B.alloca 0uy (in_extlength + 1ul) in
  let out_extra = B.alloca 0uy (in_extlength + 1ul) in

  let in_extra = B.sub in_extra 0ul in_extlength in
  let out_extra = B.sub out_extra 0ul in_extlength in

  // Copy the initial contents in these buffers
  B.blit in_b 0ul in_extra 0ul num_bytes';

  let h0 = get() in
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h0 in_extra)) (UInt64.v num_bytes))
    (seq_uint8_to_seq_nat8 (B.as_seq h0 in_b)));

  let _ = gctr256_bytes_stdcall' key in_extra num_bytes out_extra keys_b ctr_b in

  B.blit out_extra 0ul out_b 0ul num_bytes';

  let h1 = get() in
  assert (Seq.equal
    (slice_work_around (seq_uint8_to_seq_nat8 (B.as_seq h1 out_extra)) (UInt64.v num_bytes))
    (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)));

  pop_frame()
