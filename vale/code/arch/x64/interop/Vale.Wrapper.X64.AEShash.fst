module Vale.Wrapper.X64.AEShash

open FStar.Mul
open Vale.Stdcalls.X64.AesHash
open Vale.AsLowStar.MemoryHelpers
open Vale.X64.MemoryAdapters
open Vale.Arch.Types

open Vale.AES.Gcm_simplify
open Vale.SHA.Simplify_Sha

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


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


let length_aux5 (b:uint8_p) : Lemma
  (requires B.length b = 128)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db

#push-options "--z3cliopt smt.arith.nl=true"
inline_for_extraction
let aes128_keyhash_init_stdcall key roundkeys_b hkeys_b =
  let h0 = get() in

  DV.length_eq (get_downview roundkeys_b);
  DV.length_eq (get_downview hkeys_b);

  let lemma_aux1 () : Lemma
    (let db = get_downview roundkeys_b in
     length_aux roundkeys_b;
     let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
     Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    = let db = get_downview roundkeys_b in
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 roundkeys_b h0;
      Vale.Def.Words.Seq.seq_nat8_to_seq_uint8_injective (le_seq_quad32_to_bytes (UV.as_seq h0 ub))
         (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 (Ghost.reveal key)));
      le_seq_quad32_to_bytes_injective (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key))
  in lemma_aux1 ();

  let (x, _) = aes128_keyhash_init key roundkeys_b hkeys_b () in

  let h1 = get() in


  let lemma_aux2 () : Lemma
    (let db = get_downview hkeys_b in
      length_aux5 hkeys_b;
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      UV.as_seq h1 ub == le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b)))
    = let db = get_downview hkeys_b in
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 hkeys_b h1;
      le_bytes_to_seq_quad32_to_bytes (UV.as_seq h1 ub)
  in lemma_aux2 ()
#pop-options

#push-options "--z3cliopt smt.arith.nl=true"
inline_for_extraction
let aes256_keyhash_init_stdcall key roundkeys_b hkeys_b =
  let h0 = get() in

  DV.length_eq (get_downview roundkeys_b);
  DV.length_eq (get_downview hkeys_b);

  let lemma_aux1 () : Lemma
    (let db = get_downview roundkeys_b in
     length_aux2 roundkeys_b;
     let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
     Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_256 (Ghost.reveal key)))
    = let db = get_downview roundkeys_b in
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 roundkeys_b h0;
      Vale.Def.Words.Seq.seq_nat8_to_seq_uint8_injective (le_seq_quad32_to_bytes (UV.as_seq h0 ub))
         (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_256 (Ghost.reveal key)));
      le_seq_quad32_to_bytes_injective (UV.as_seq h0 ub) (key_to_round_keys_LE AES_256 (Ghost.reveal key))
  in lemma_aux1 ();

  let (x, _) = aes256_keyhash_init key roundkeys_b hkeys_b () in

  let h1 = get() in

  let lemma_aux2 () : Lemma
    (let db = get_downview hkeys_b in
      length_aux5 hkeys_b;
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      UV.as_seq h1 ub == le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b)))
    = let db = get_downview hkeys_b in
      let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
      lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 hkeys_b h1;
      le_bytes_to_seq_quad32_to_bytes (UV.as_seq h1 ub)
  in lemma_aux2 ()
#pop-options
