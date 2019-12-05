module Vale.Wrapper.X64.AES

open FStar.Mul
open Vale.Stdcalls.X64.Aes
open Vale.AsLowStar.MemoryHelpers
open Vale.X64.MemoryAdapters
open Vale.Arch.Types

open Vale.AES.Gcm_simplify
open Vale.SHA.Simplify_Sha

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
#set-options "--z3cliopt smt.arith.nl=true"

let aes128_key_expansion_stdcall input_b output_b =
  let h0 = get() in

  DV.length_eq (get_downview input_b);
  DV.length_eq (get_downview output_b);

  let (x, _) = aes128_key_expansion input_b output_b () in

  let h1 = get() in


  let lemma_aux () : Lemma
    (let key = seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (B.as_seq h0 input_b)) in
      Seq.equal (B.as_seq h1 output_b)
         (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_128 key))))
     = let key = seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (B.as_seq h0 input_b)) in
       let db = get_downview output_b in
       length_aux output_b;
       let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
       aes_simplify1 input_b h0;
       assert (Seq.equal (UV.as_seq h1 ub) (key_to_round_keys_LE AES_128 key));
       calc (==) {
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 output_b));
        (==) { lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 output_b h1 }
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (UV.as_seq h1 ub))));
        (==) { le_bytes_to_seq_quad32_to_bytes (UV.as_seq h1 ub) }
        UV.as_seq h1 ub;
      };
      le_seq_quad32_to_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 output_b))

  in lemma_aux()

let aes256_key_expansion_stdcall input_b output_b =
  let h0 = get() in

  DV.length_eq (get_downview input_b);
  DV.length_eq (get_downview output_b);

  let (x, _) = aes256_key_expansion input_b output_b () in

  let h1 = get() in

  let lemma_aux () : Lemma
    (let key = seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (B.as_seq h0 input_b)) in
      Seq.equal (B.as_seq h1 output_b)
         (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE AES_256 key))))
     = let key = seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (B.as_seq h0 input_b)) in
       let db = get_downview output_b in
       length_aux2 output_b;
       let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
       aes_simplify2 input_b h0;
       assert (Seq.equal (UV.as_seq h1 ub) (key_to_round_keys_LE AES_256 key));
       calc (==) {
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 output_b));
        (==) { lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 output_b h1 }
        le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (UV.as_seq h1 ub))));
        (==) { le_bytes_to_seq_quad32_to_bytes (UV.as_seq h1 ub) }
        UV.as_seq h1 ub;
      };
      le_seq_quad32_to_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 output_b))

  in lemma_aux()
