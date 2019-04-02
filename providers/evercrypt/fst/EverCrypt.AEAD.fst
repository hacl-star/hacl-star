module EverCrypt.AEAD

module S = FStar.Seq
module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Integers
open FStar.Int.Cast

open Spec.AEAD

friend Spec.AEAD

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let ekv_len (a: supported_alg): Tot (x:UInt32.t { UInt32.v x = ekv_length a }) =
  match a with
  | CHACHA20_POLY1305 -> 32ul
  | AES128_GCM -> 176ul + 128ul
  | AES256_GCM -> 240ul + 128ul

let expand_in #a r k =
  match a with
  | AES128_GCM ->
      let h0 = ST.get () in
      let kv: G.erased (kv a) = G.hide (B.as_seq h0 k) in
      let has_aesni = EverCrypt.AutoConfig2.has_aesni () in
      let has_pclmulqdq = EverCrypt.AutoConfig2.has_pclmulqdq () in
      if EverCrypt.TargetConfig.x64 && (has_aesni && has_pclmulqdq) then (
        let ek =
          MB.mmalloc #UInt8.t #(frozen_preorder (expand #a (G.reveal kv))) r 0uy (ekv_len a)
        in
        push_frame();
        let ek' =
          B.alloca #UInt8.t 0uy 304ul
        in
        let keys_b = B.sub ek' 0ul 176ul in
        let hkeys_b = B.sub ek' 176ul 128ul in
        AES_stdcalls.aes128_key_expansion_stdcall k keys_b;
        AEShash_stdcalls.aes128_keyhash_init_stdcall
          (let k = G.reveal kv in
          let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
          let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
          keys_b hkeys_b;
        let h1 = ST.get() in

        // Since ek has a frozen preorder, we need to prove that we are copying the
        // expanded key into it. In particular, that the hashed part corresponds to the spec
        let lemma_aux_hkeys () : Lemma
          (let k = G.reveal kv in
           let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
           let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
           let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
             AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
           let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
           Seq.equal (B.as_seq h1 hkeys_b) hkeys)
           = let k = G.reveal kv in
             let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
             let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
             let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
               AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
             let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
            Gcm_simplify.le_bytes_to_seq_quad32_uint8_to_nat8_length (B.as_seq h1 hkeys_b);
            assert_norm (128 / 16 = 8);
            // These two are equal
            OptPublic.get_hkeys_reqs_injective
              (Types_s.reverse_bytes_quad32 (
               AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0)))
              hkeys_quad
              (Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b)));
            Arch.Types.le_seq_quad32_to_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b))

        in lemma_aux_hkeys ();
                   
        MB.blit ek' 0ul ek 0ul 304ul;
        pop_frame();
        let h2 = ST.get() in
        assert (Seq.equal (B.as_seq h2 ek)  (expand #a (G.reveal kv)));
        B.modifies_only_not_unused_in B.loc_none h0 h2;
        MB.witness_p ek (S.equal (expand #a (G.reveal kv)));
        EK kv ek
      ) else
        EK kv MB.mnull

  | AES256_GCM -> 
      let h0 = ST.get () in
      let kv: G.erased (kv a) = G.hide (B.as_seq h0 k) in
      let has_aesni = EverCrypt.AutoConfig2.has_aesni () in
      let has_pclmulqdq = EverCrypt.AutoConfig2.has_pclmulqdq () in
      if EverCrypt.TargetConfig.x64 && (has_aesni && has_pclmulqdq) then (
        let ek =
          MB.mmalloc #UInt8.t #(frozen_preorder (expand #a (G.reveal kv))) r 0uy (ekv_len a)
        in
        push_frame();
        let ek' =
          B.alloca #UInt8.t 0uy 368ul
        in
        let keys_b = B.sub ek' 0ul 240ul in
        let hkeys_b = B.sub ek' 240ul 128ul in
        AES_stdcalls.aes256_key_expansion_stdcall k keys_b;
        AEShash_stdcalls.aes256_keyhash_init_stdcall     
          (let k = G.reveal kv in
          let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
          let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
          keys_b hkeys_b;
        let h1 = ST.get() in

        // Since ek has a frozen preorder, we need to prove that we are copying the
        // expanded key into it. In particular, that the hashed part corresponds to the spec
        let lemma_aux_hkeys () : Lemma
          (let k = G.reveal kv in
           let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
           let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
           let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
             AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
           let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
           Seq.equal (B.as_seq h1 hkeys_b) hkeys)
           = let k = G.reveal kv in
             let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
             let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
             let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
               AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
             let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
            Gcm_simplify.le_bytes_to_seq_quad32_uint8_to_nat8_length (B.as_seq h1 hkeys_b);
            assert_norm (128 / 16 = 8);
            // These two are equal
            OptPublic.get_hkeys_reqs_injective
              (Types_s.reverse_bytes_quad32 (
               AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0)))
              hkeys_quad
              (Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b)));
            Arch.Types.le_seq_quad32_to_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b))

        in lemma_aux_hkeys ();
        
        MB.blit ek' 0ul ek 0ul 368ul;
        pop_frame();
        let h2 = ST.get() in
        assert (Seq.equal (B.as_seq h2 ek)  (expand #a (G.reveal kv)));
        B.modifies_only_not_unused_in B.loc_none h0 h2;
        MB.witness_p ek (S.equal (expand #a (G.reveal kv)));
        EK kv ek
      ) else
        EK kv MB.mnull  

  | CHACHA20_POLY1305 ->
      let h0 = ST.get () in
      let kv: G.erased (kv a) = G.hide (B.as_seq h0 k) in
      let ek = MB.mmalloc #UInt8.t #(frozen_preorder (expand #a (G.reveal kv))) r 0uy 32ul in
      MB.blit k 0ul ek 0ul 32ul;
      let h2 = ST.get () in
      B.modifies_only_not_unused_in B.loc_none h0 h2;
      assert (B.as_seq h2 ek == B.as_seq h0 k);
      MB.witness_p ek (S.equal (G.reveal kv));
      EK kv ek

  | _ ->
      EK (G.hide (S.empty #UInt8.t)) MB.mnull

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"
let encrypt #a ek iv ad ad_len plain plain_len cipher tag =
  if MB.is_null (EK?.ek ek) then
    InvalidKey
  else match a with
  | AES128_GCM ->
      // From the well-formedness invariant: the only implementation we
      // (currently) know how to use on X64 is Vale's. In the future, we will
      // have to either:
      // - have a run-time representation of expanded keys that is uniform
      //   (preferred), or
      // - add a run-time tag that indicates which implementation we're running
      //   with (and cover that with the wf invariant).
      MB.recall_p (EK?.ek ek) (S.equal (expand_or_dummy a (EK?.kv ek)));
      assert (EverCrypt.TargetConfig.x64 /\ X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled));
      assert (is_supported_alg a /\ not (MB.g_is_null (EK?.ek ek)));

      assert (
        let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

      push_frame();
      // Cannot pass a frozen buffer to a function that expects a regular
      // buffer. (Or can we? Prove compatibility of preorders?). In any case, we
      // just allocate a temporary on the stack and blit.
      let tmp_keys = B.alloca 0uy 176ul in
      MB.blit (EK?.ek ek) 0ul tmp_keys 0ul 176ul;      

      let hkeys_b = B.alloca 0uy 128ul in
      MB.blit (EK?.ek ek) 176ul hkeys_b 0ul 128ul;

      let h0 = get() in

      // The iv is modified by Vale, which the API does not allow. Hence
      // we allocate a temporary buffer and blit the contents of the iv
      let tmp_iv = B.alloca 0uy 16ul in
      let h_pre = get() in
      
      MB.blit iv 0ul tmp_iv 0ul 12ul;

      let h0 = get() in

      // Some help is needed to prove that the end of the tmp_iv buffer
      // is still 0s after blitting the contents of iv into the start of the buffer
      let lemma_iv_eq () : Lemma 
        (let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
        Seq.equal
          (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv))
          iv_nat)
        = let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
          let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
          let s_tmp = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv) in
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 0;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 1;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 2;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 3;          
          assert (Seq.equal iv_nat s_tmp)
          

      in lemma_iv_eq ();

      // There is no SMTPat on le_bytes_to_seq_quad32_to_bytes and the converse,
      // so we need an explicit lemma
      let lemma_hkeys_reqs () : Lemma
        (let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        OptPublic.hkeys_reqs_pub 
          (Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
          (Types_s.reverse_bytes_quad32 (AES_s.aes_encrypt_LE AES_s.AES_128 k_w (Words_s.Mkfour 0 0 0 0)))) 
        = let k = G.reveal (EK?.kv ek) in
          let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
          let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
          let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
            AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
          let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
          assert (Seq.equal (B.as_seq h0 hkeys_b) hkeys);
          calc (==) {
            Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 hkeys);
            (==) { Arch.Types.le_bytes_to_seq_quad32_to_bytes hkeys_quad }
            hkeys_quad;
          }

      in lemma_hkeys_reqs ();

      // These asserts prove that 4096 * (len {plain, ad}) are smaller than pow2_32
      assert (max_length a = pow2 20 - 1 - 16);
      assert_norm (4096 * (pow2 20 - 1) < Words_s.pow2_32);
      assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);

      GCMencryptOpt_stdcalls.gcm128_encrypt_opt_stdcall
        (let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
        plain
        (uint32_to_uint64 plain_len)
        ad
        (uint32_to_uint64 ad_len)
        tmp_iv
        cipher
        tag
        tmp_keys
        hkeys_b;

      let h1 = get() in

      // This assert is needed for z3 to pick up sequence equality for ciphertext
      // and tag. It could be avoided if the spec returned both instead of appending them
      assert (   
        let kv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (G.reveal (EK?.kv ek)) in
        let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        // the specification takes a seq16 for convenience, but actually discards
        // the trailing four bytes; we are, however, constrained by it and append
        // zeroes just to satisfy the spec
        let iv_nat = S.append iv_nat (S.create 4 0) in
        // `ad` is called `auth` in Vale world; "additional data", "authenticated
        // data", potato, potato
        let ad_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 ad) in
        let plain_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 plain) in
        assert (max_length a = pow2 20 - 1 - 16);
        assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);
        let cipher_nat, tag_nat =
          GCM_s.gcm_encrypt_LE (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat
        in
        Seq.equal (B.as_seq h1 cipher) (Words.Seq_s.seq_nat8_to_seq_uint8 cipher_nat) /\
        Seq.equal (B.as_seq h1 tag) (Words.Seq_s.seq_nat8_to_seq_uint8 tag_nat));


      pop_frame();
      Success

  | AES256_GCM ->
      // From the well-formedness invariant: the only implementation we
      // (currently) know how to use on X64 is Vale's. In the future, we will
      // have to either:
      // - have a run-time representation of expanded keys that is uniform
      //   (preferred), or
      // - add a run-time tag that indicates which implementation we're running
      //   with (and cover that with the wf invariant).
      MB.recall_p (EK?.ek ek) (S.equal (expand_or_dummy a (EK?.kv ek)));
      assert (EverCrypt.TargetConfig.x64 /\ X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled));
      assert (is_supported_alg a /\ not (MB.g_is_null (EK?.ek ek)));

      assert (
        let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

      push_frame();
      // Cannot pass a frozen buffer to a function that expects a regular
      // buffer. (Or can we? Prove compatibility of preorders?). In any case, we
      // just allocate a temporary on the stack and blit.
      let tmp_keys = B.alloca 0uy 240ul in
      MB.blit (EK?.ek ek) 0ul tmp_keys 0ul 240ul;      

      let hkeys_b = B.alloca 0uy 128ul in
      MB.blit (EK?.ek ek) 240ul hkeys_b 0ul 128ul;

      let h0 = get() in

      // The iv is modified by Vale, which the API does not allow. Hence
      // we allocate a temporary buffer and blit the contents of the iv
      let tmp_iv = B.alloca 0uy 16ul in
      let h_pre = get() in
      
      MB.blit iv 0ul tmp_iv 0ul 12ul;

      let h0 = get() in

      // Some help is needed to prove that the end of the tmp_iv buffer
      // is still 0s after blitting the contents of iv into the start of the buffer
      let lemma_iv_eq () : Lemma 
        (let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
        Seq.equal
          (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv))
          iv_nat)
        = let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
          let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
          let s_tmp = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv) in
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 0;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 1;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 2;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 3;          
          assert (Seq.equal iv_nat s_tmp)

      in lemma_iv_eq ();

      // There is no SMTPat on le_bytes_to_seq_quad32_to_bytes and the converse,
      // so we need an explicit lemma
      let lemma_hkeys_reqs () : Lemma
        (let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        OptPublic.hkeys_reqs_pub 
          (Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 hkeys_b)))
          (Types_s.reverse_bytes_quad32 (AES_s.aes_encrypt_LE AES_s.AES_256 k_w (Words_s.Mkfour 0 0 0 0)))) 
        = let k = G.reveal (EK?.kv ek) in
          let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
          let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
          let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
            AES_s.aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
          let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
          assert (Seq.equal (B.as_seq h0 hkeys_b) hkeys);
          calc (==) {
            Types_s.le_bytes_to_seq_quad32 (Words.Seq_s.seq_uint8_to_seq_nat8 hkeys);
            (==) { Arch.Types.le_bytes_to_seq_quad32_to_bytes hkeys_quad }
            hkeys_quad;
          }

      in lemma_hkeys_reqs ();

      // These asserts prove that 4096 * (len {plain, ad}) are smaller than pow2_32
      assert (max_length a = pow2 20 - 1 - 16);
      assert_norm (4096 * (pow2 20 - 1) < Words_s.pow2_32);
      assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);

      GCMencryptOpt256_stdcalls.gcm256_encrypt_opt_stdcall
        (let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
        plain
        (uint32_to_uint64 plain_len)
        ad
        (uint32_to_uint64 ad_len)
        tmp_iv
        cipher
        tag
        tmp_keys
        hkeys_b;

      let h1 = get() in

      // This assert is needed for z3 to pick up sequence equality for ciphertext
      // and tag. It could be avoided if the spec returned both instead of appending them
      assert (   
        let kv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (G.reveal (EK?.kv ek)) in
        let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        // the specification takes a seq16 for convenience, but actually discards
        // the trailing four bytes; we are, however, constrained by it and append
        // zeroes just to satisfy the spec
        let iv_nat = S.append iv_nat (S.create 4 0) in
        // `ad` is called `auth` in Vale world; "additional data", "authenticated
        // data", potato, potato
        let ad_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 ad) in
        let plain_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 plain) in
        assert (max_length a = pow2 20 - 1 - 16);
        assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);
        let cipher_nat, tag_nat =
          GCM_s.gcm_encrypt_LE (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat
        in
        Seq.equal (B.as_seq h1 cipher) (Words.Seq_s.seq_nat8_to_seq_uint8 cipher_nat) /\
        Seq.equal (B.as_seq h1 tag) (Words.Seq_s.seq_nat8_to_seq_uint8 tag_nat));


      pop_frame();
      Success

  | CHACHA20_POLY1305 ->
      // Monotonicity; gives us proper length for ek while we're at it.
      MB.recall_p (EK?.ek ek) (S.equal (expand_or_dummy a (EK?.kv ek)));
      assert (MB.length (EK?.ek ek) = 32);
      assert (B.length iv = 12);

      push_frame ();
      // Cannot pass a frozen buffer to a function that expects a regular
      // buffer. (Or can we? Prove compatibility of preorders?). In any case, we
      // just allocate a temporary on the stack and blit.
      let tmp = B.alloca 0uy 32ul in
      MB.blit (EK?.ek ek) 0ul tmp 0ul 32ul;

      // Length restrictions
      assert_norm (pow2 31 + pow2 32 / 64 <= pow2 32 - 1);

      Hacl.Impl.Chacha20Poly1305.aead_encrypt_chacha_poly
        tmp iv ad_len ad plain_len plain cipher tag;
      pop_frame ();
      Success


#set-options "--z3rlimit 200"
let decrypt #a ek iv ad ad_len cipher cipher_len tag dst =
  if MB.is_null (EK?.ek ek) then
    InvalidKey

  else match a with
  | AES128_GCM ->
      // See comments for encrypt above
      MB.recall_p (EK?.ek ek) (S.equal (expand_or_dummy a (EK?.kv ek)));
      assert (EverCrypt.TargetConfig.x64 /\ X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled));
      assert (is_supported_alg a /\ not (MB.g_is_null (EK?.ek ek)));

      assert (
        let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

      push_frame();
      // Cannot pass a frozen buffer to a function that expects a regular
      // buffer. (Or can we? Prove compatibility of preorders?). In any case, we
      // just allocate a temporary on the stack and blit.
      let tmp_keys = B.alloca 0uy 176ul in
      MB.blit (EK?.ek ek) 0ul tmp_keys 0ul 176ul;
      
      // The iv is modified by Vale, which the API does not allow. Hence
      // we allocate a temporary buffer and blit the contents of the iv
      let tmp_iv = B.alloca 0uy 16ul in
      let h_pre = get() in
      
      MB.blit iv 0ul tmp_iv 0ul 12ul;

      let h0 = get() in

      // Some help is needed to prove that the end of the tmp_iv buffer
      // is still 0s after blitting the contents of iv into the start of the buffer
      let lemma_iv_eq () : Lemma 
        (let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
        Seq.equal
          (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv))
          iv_nat)
        = let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
          let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
          let s_tmp = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv) in
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 0;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 1;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 2;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 3;          
          assert (Seq.equal iv_nat s_tmp)
          

      in lemma_iv_eq ();

      // These asserts prove that 4096 * (len {cipher, ad}) are smaller than pow2_32
      assert (max_length a = pow2 20 - 1 - 16);
      assert_norm (4096 * (pow2 20 - 1) < Words_s.pow2_32);
      assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);

      let h0 = get() in 

      let r = GCMdecrypt_stdcalls.gcm128_decrypt_stdcall
        (let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
        cipher
        (uint32_to_uint64 cipher_len)
        ad
        (uint32_to_uint64 ad_len)
        tmp_iv
        dst
        tag
        tmp_keys in

      let h1 = get() in

      // This assert is needed for z3 to pick up sequence equality for ciphertext
      // It could be avoided if the spec returned both instead of appending them
      assert (   
        let kv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (G.reveal (EK?.kv ek)) in      
        let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        // the specification takes a seq16 for convenience, but actually discards
        // the trailing four bytes; we are, however, constrained by it and append
        // zeroes just to satisfy the spec
        let iv_nat = S.append iv_nat (S.create 4 0) in
        // `ad` is called `auth` in Vale world; "additional data", "authenticated
        // data", potato, potato
        let ad_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 ad) in
        let cipher_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 cipher) in
        let tag_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tag) in
        assert (max_length a = pow2 20 - 1 - 16);
        assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);
        let plain_nat, success =
          GCM_s.gcm_decrypt_LE (vale_alg_of_alg a) kv_nat iv_nat cipher_nat ad_nat tag_nat
        in
        Seq.equal (B.as_seq h1 dst) (Words.Seq_s.seq_nat8_to_seq_uint8 plain_nat) /\
        (UInt64.v r = 0) == success);

      assert (
        let kv = G.reveal (EK?.kv ek) in
        let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
        Seq.equal (Seq.slice cipher_tag (S.length cipher_tag - tag_length a) (S.length cipher_tag))
          (B.as_seq h0 tag) /\
        Seq.equal (Seq.slice cipher_tag 0 (S.length cipher_tag - tag_length a)) (B.as_seq h0 cipher));

      pop_frame();

      if r = 0uL then
        Success
      else
        Failure

  | AES256_GCM ->
        // See comments for encrypt above
      MB.recall_p (EK?.ek ek) (S.equal (expand_or_dummy a (EK?.kv ek)));
      assert (EverCrypt.TargetConfig.x64 /\ X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled));
      assert (is_supported_alg a /\ not (MB.g_is_null (EK?.ek ek)));

      assert (
        let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
        AES_s.is_aes_key_LE (vale_alg_of_alg a) k_w);

      push_frame();
      // Cannot pass a frozen buffer to a function that expects a regular
      // buffer. (Or can we? Prove compatibility of preorders?). In any case, we
      // just allocate a temporary on the stack and blit.
      let tmp_keys = B.alloca 0uy 240ul in
      MB.blit (EK?.ek ek) 0ul tmp_keys 0ul 240ul;
      
      // The iv is modified by Vale, which the API does not allow. Hence
      // we allocate a temporary buffer and blit the contents of the iv
      let tmp_iv = B.alloca 0uy 16ul in
      let h_pre = get() in
      
      MB.blit iv 0ul tmp_iv 0ul 12ul;

      let h0 = get() in

      // Some help is needed to prove that the end of the tmp_iv buffer
      // is still 0s after blitting the contents of iv into the start of the buffer
      let lemma_iv_eq () : Lemma 
        (let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
        Seq.equal
          (Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv))
          iv_nat)
        = let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
          let iv_nat = Seq.append iv_nat (Seq.create 4 0) in
          let s_tmp = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tmp_iv) in
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 0;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 1;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 2;
          Seq.lemma_index_slice (B.as_seq h0 tmp_iv) 12 16 3;          
          assert (Seq.equal iv_nat s_tmp)
          

      in lemma_iv_eq ();

      // These asserts prove that 4096 * (len {cipher, ad}) are smaller than pow2_32
      assert (max_length a = pow2 20 - 1 - 16);
      assert_norm (4096 * (pow2 20 - 1) < Words_s.pow2_32);
      assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);

      let r = GCMdecrypt_stdcalls.gcm256_decrypt_stdcall
        (let k = G.reveal (EK?.kv ek) in
        let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
        let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in G.hide k_w)
        cipher
        (uint32_to_uint64 cipher_len)
        ad
        (uint32_to_uint64 ad_len)
        tmp_iv
        dst
        tag
        tmp_keys in

      let h1 = get() in

      // This assert is needed for z3 to pick up sequence equality for ciphertext
      // It could be avoided if the spec returned both instead of appending them
      assert (   
        let kv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (G.reveal (EK?.kv ek)) in      
        let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 iv) in
        // the specification takes a seq16 for convenience, but actually discards
        // the trailing four bytes; we are, however, constrained by it and append
        // zeroes just to satisfy the spec
        let iv_nat = S.append iv_nat (S.create 4 0) in
        // `ad` is called `auth` in Vale world; "additional data", "authenticated
        // data", potato, potato
        let ad_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 ad) in
        let cipher_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 cipher) in
        let tag_nat = Words.Seq_s.seq_uint8_to_seq_nat8 (B.as_seq h0 tag) in
        assert (max_length a = pow2 20 - 1 - 16);
        assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);
        let plain_nat, success =
          GCM_s.gcm_decrypt_LE (vale_alg_of_alg a) kv_nat iv_nat cipher_nat ad_nat tag_nat
        in
        Seq.equal (B.as_seq h1 dst) (Words.Seq_s.seq_nat8_to_seq_uint8 plain_nat) /\
        (UInt64.v r = 0) == success);

      assert (
        let kv = G.reveal (EK?.kv ek) in
        let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
        Seq.equal (Seq.slice cipher_tag (S.length cipher_tag - tag_length a) (S.length cipher_tag))
          (B.as_seq h0 tag) /\
        Seq.equal (Seq.slice cipher_tag 0 (S.length cipher_tag - tag_length a)) (B.as_seq h0 cipher));

      pop_frame();

      if r = 0uL then
        Success
      else
        Failure
  
  | CHACHA20_POLY1305 ->
      // See comments for encrypt above
      MB.recall_p (EK?.ek ek) (S.equal (expand_or_dummy a (EK?.kv ek)));
      assert (MB.length (EK?.ek ek) = 32);
      assert (B.length iv = 12);

      push_frame ();

      let tmp = B.alloca 0uy 32ul in
      MB.blit (EK?.ek ek) 0ul tmp 0ul 32ul;

      [@ inline_let ] let bound = pow2 32 - 1 - 16 in
      assert (v cipher_len <= bound);
      assert_norm (bound + 16 <= pow2 32 - 1);
      assert_norm (pow2 31 + bound / 64 <= pow2 32 - 1);

      let h0 = ST.get () in
      let r = Hacl.Impl.Chacha20Poly1305.aead_decrypt_chacha_poly
        tmp iv ad_len ad cipher_len dst cipher tag
      in
      assert (
        let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
        let tag_s = S.slice cipher_tag (S.length cipher_tag - tag_length a) (S.length cipher_tag) in
        let cipher_s = S.slice cipher_tag 0 (S.length cipher_tag - tag_length a) in
        S.equal cipher_s (B.as_seq h0 cipher) /\ S.equal tag_s (B.as_seq h0 tag));
      pop_frame ();
      if r = 0ul then
        Success
      else
        Failure
