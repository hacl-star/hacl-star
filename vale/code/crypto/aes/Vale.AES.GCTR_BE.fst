module Vale.AES.GCTR_BE

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open FStar.Seq
open Vale.AES.AES_BE_s
open Vale.AES.GCTR_BE_s
open Vale.AES.GCM_helpers_BE
open FStar.Math.Lemmas
open Vale.Lib.Seqs
open Vale.AES.Types_helpers

let gctr_encrypt_block_offset (icb:quad32) (plain:quad32) (alg:algorithm) (key:seq nat32) (i:int) =
  ()

let gctr_partial_opaque_init alg plain cipher key icb =
  gctr_partial_reveal ();
  ()

#restart-solver
let lemma_gctr_partial_append alg b1 b2 p1 c1 p2 c2 key icb1 icb2 =
  gctr_partial_reveal ();
  ()

let gctr_partial_opaque_ignores_postfix alg bound plain plain' cipher cipher' key icb =
  gctr_partial_reveal ();
  // OBSERVE:
  assert (forall i . 0 <= i /\ i < bound ==> index plain i == index (slice plain 0 bound) i);
  assert (forall i . 0 <= i /\ i < bound ==> index plain' i == index (slice plain' 0 bound) i);
  assert (forall i . 0 <= i /\ i < bound ==> index cipher i == index (slice cipher 0 bound) i);
  assert (forall i . 0 <= i /\ i < bound ==> index cipher' i == index (slice cipher' 0 bound) i);
  ()

let rec gctr_encrypt_recursive_length (icb:quad32) (plain:gctr_plain_internal)
                                      (alg:algorithm) (key:aes_key_word alg) (i:int) : Lemma
  (requires True)
  (ensures length (gctr_encrypt_recursive icb plain alg key i) == length plain)
  (decreases %[length plain])
  [SMTPat (length (gctr_encrypt_recursive icb plain alg key i))]
  =
  if length plain = 0 then ()
  else gctr_encrypt_recursive_length icb (tail plain) alg key (i + 1)

//TODO: Check if ever being used
#reset-options "--z3rlimit 40"
let gctr_encrypt_length (icb:quad32) (plain:gctr_plain)
                             (alg:algorithm) (key:aes_key_word alg) :
  Lemma(length (gctr_encrypt icb plain alg key) == length plain)
  [SMTPat (length (gctr_encrypt icb plain alg key))]
  =
  reveal_opaque (`%be_bytes_to_seq_quad32) be_bytes_to_seq_quad32;
  gctr_encrypt_reveal ();
  let num_extra = (length plain) % 16 in
  let result = gctr_encrypt icb plain alg key in
  if num_extra = 0 then (
    let plain_quads = be_bytes_to_seq_quad32 plain in
    gctr_encrypt_recursive_length icb plain_quads alg key 0
  ) else (
    let full_bytes_len = (length plain) - num_extra in
    let full_blocks, final_block = split plain full_bytes_len in

    let full_quads = be_bytes_to_seq_quad32 full_blocks in
    let final_quad = be_bytes_to_quad32 (pad_to_128_bits final_block) in

    let cipher_quads = gctr_encrypt_recursive icb full_quads alg key 0 in
    let final_cipher_quad = gctr_encrypt_block icb final_quad alg key (full_bytes_len / 16) in

    let cipher_bytes_full = seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_quads) in
    let final_cipher_bytes = slice (be_quad32_to_bytes final_cipher_quad) 0 num_extra in

    gctr_encrypt_recursive_length icb full_quads alg key 0;
    assert (length result == length cipher_bytes_full + length final_cipher_bytes);
    assert (length cipher_quads == length full_quads);
    assert (length cipher_bytes_full == 16 * length cipher_quads);
    assert (16 * length full_quads == length full_blocks);
    assert (length cipher_bytes_full == length full_blocks);
    ()
  )
#reset-options

let rec gctr_indexed_helper (icb:quad32) (plain:gctr_plain_internal)
                            (alg:algorithm) (key:aes_key_word alg) (i:int) : Lemma
  (requires True)
  (ensures (let cipher = gctr_encrypt_recursive icb plain alg key i in
            length cipher == length plain /\
           (forall j . {:pattern index cipher j} 0 <= j /\ j < length plain ==>
           index cipher j == quad32_xor (index plain j) (aes_encrypt_word alg key (inc32 icb (i + j)) ))))
  (decreases %[length plain])
=
  if length plain = 0 then ()
  else
      let tl = tail plain in
      let cipher = gctr_encrypt_recursive icb plain alg key i in
      let r_cipher = gctr_encrypt_recursive icb tl alg key (i+1) in
      let helper (j:int) :
        Lemma ((0 <= j /\ j < length plain) ==> (index cipher j == quad32_xor (index plain j) (aes_encrypt_word alg key (inc32 icb (i + j)) )))
        =
        aes_encrypt_word_reveal ();
        if 0 < j && j < length plain then (
          gctr_indexed_helper icb tl alg key (i+1);
          assert(index r_cipher (j-1) == quad32_xor (index tl (j-1)) (aes_encrypt_word alg key (inc32 icb (i + 1 + j - 1)) )) // OBSERVE
        ) else ()
      in
      FStar.Classical.forall_intro helper

let gctr_indexed (icb:quad32) (plain:gctr_plain_internal)
                     (alg:algorithm) (key:aes_key_word alg) (cipher:seq quad32) : Lemma
  (requires  length cipher == length plain /\
             (forall i . {:pattern index cipher i} 0 <= i /\ i < length cipher ==>
             index cipher i == quad32_xor (index plain i) (aes_encrypt_word alg key (inc32 icb i) )))
  (ensures  cipher == gctr_encrypt_recursive icb plain alg key 0)
=
  gctr_indexed_helper icb plain alg key 0;
  let c = gctr_encrypt_recursive icb plain alg key 0 in
  assert(equal cipher c)  // OBSERVE: Invoke extensionality lemmas

let gctr_partial_completed (alg:algorithm) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) =
  gctr_indexed icb plain alg key cipher;
  ()

let gctr_partial_opaque_completed (alg:algorithm) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires
    is_aes_key_word alg key /\
    length plain == length cipher /\
    length plain < pow2_32 /\
    gctr_partial alg (length cipher) plain cipher key icb
  )
  (ensures cipher == gctr_encrypt_recursive icb plain alg key 0)
  =
  gctr_partial_reveal ();
  gctr_partial_completed alg plain cipher key icb

let gctr_partial_to_full_basic (icb:quad32) (plain:seq quad32) (alg:algorithm) (key:seq nat32) (cipher:seq quad32) =
  gctr_encrypt_reveal ();
  let p = seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain) in
  assert (length p % 16 == 0);
  let plain_quads = be_bytes_to_seq_quad32 p in
  let cipher_quads = gctr_encrypt_recursive icb plain_quads alg key 0 in
  let cipher_bytes = seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_quads) in
  be_bytes_to_seq_quad32_to_bytes plain;
  ()

let step1 (p:seq quad32) (num_bytes:nat{ num_bytes < 16 * length p }) : Lemma
  (let num_extra = num_bytes % 16 in
   let num_blocks = num_bytes / 16 in
   let full_blocks, final_block = split (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE p)) 0 num_bytes) (num_blocks * 16) in
   let full_quads_BE = be_bytes_to_seq_quad32 full_blocks in
   let p_prefix = slice p 0 num_blocks in
   p_prefix == full_quads_BE)
  =
  let num_extra = num_bytes % 16 in
  let num_blocks = num_bytes / 16 in
  let full_blocks, final_block = split (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE p)) 0 num_bytes) (num_blocks * 16) in
  let full_quads_BE = be_bytes_to_seq_quad32 full_blocks in
  let p_prefix = slice p 0 num_blocks in
  assert (length full_blocks == num_blocks * 16);
  assert (full_blocks == slice (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE p)) 0 num_bytes) 0 (num_blocks * 16));
  assert (full_blocks == slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE p)) 0 (num_blocks * 16));
  slice_commutes_be_seq_quad32_to_bytes0 p num_blocks;
  assert (full_blocks == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice p 0 num_blocks)));
  be_bytes_to_seq_quad32_to_bytes (slice p 0 num_blocks);
  assert (full_quads_BE == (slice p 0 num_blocks));
  ()

#reset-options "--smtencoding.elim_box true --z3rlimit 30"
let lemma_slice_orig_index (#a:Type) (s s':seq a) (m n:nat) : Lemma
  (requires length s == length s' /\ m <= n /\ n <= length s /\ slice s m n == slice s' m n)
  (ensures (forall (i:int).{:pattern (index s i) \/ (index s' i)} m <= i /\ i < n ==> index s i == index s' i))
  =
  let aux (i:nat{m <= i /\ i < n}) : Lemma (index s i == index s' i) =
    lemma_index_slice s m n (i - m);
    lemma_index_slice s' m n (i - m)
  in Classical.forall_intro aux

let lemma_ishr_ixor_32 (x y:nat32) (k:nat) : Lemma
  (ensures ishr #pow2_32 (ixor x y) k == ixor (ishr x k) (ishr y k))
  =
  Vale.Def.TypesNative_s.reveal_ishr 32 x k;
  Vale.Def.TypesNative_s.reveal_ishr 32 y k;
  Vale.Def.TypesNative_s.reveal_ishr 32 (ixor x y) k;
  Vale.Def.TypesNative_s.reveal_ixor 32 x y;
  Vale.Def.TypesNative_s.reveal_ixor 32 (ishr x k) (ishr y k);
  FStar.UInt.shift_right_logxor_lemma #32 x y k;
  ()

let nat32_xor_bytewise_1_helper1 (x0 x0':nat8) (x1 x1':nat24) (x x':nat32) : Lemma
  (requires
    x == 0x1000000 * x0 + x1 /\
    x' == 0x1000000 * x0' + x1' /\
    x / 0x1000000 == x' / 0x1000000
  )
  (ensures x0 == x0')
  =
  ()

let nat32_xor_bytewise_2_helper1 (x0 x0' x1 x1':nat16) (x x':nat32) : Lemma
  (requires
    x == 0x10000 * x0 + x1 /\
    x' == 0x10000 * x0' + x1' /\
    x / 0x10000 == x' / 0x10000
  )
  (ensures x0 == x0')
  =
  ()

let nat32_xor_bytewise_3_helper1 (x0 x0':nat24) (x1 x1':nat8) (x x':nat32) : Lemma
  (requires
    x == 0x100 * x0 + x1 /\
    x' == 0x100 * x0' + x1' /\
    x / 0x100 == x' / 0x100
  )
  (ensures x0 == x0')
  =
  ()

let nat32_xor_bytewise_1_helper2 (x x':nat32) (t t':four nat8) : Lemma
  (requires
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    x / 0x1000000 == x' / 0x1000000
  )
  (ensures t.hi3 == t'.hi3)
  =
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  let t012 = t0 + 0x100 * t1 + 0x10000 * t2 in
  let t012' = t0' + 0x100 * t1' + 0x10000 * t2' in
  assert_norm (four_to_nat 8 t  == four_to_nat_unfold 8 t );
  assert_norm (four_to_nat 8 t' == four_to_nat_unfold 8 t');
  nat32_xor_bytewise_1_helper1 t3 t3' t012 t012' x x';
  ()

let nat32_xor_bytewise_2_helper2 (x x':nat32) (t t':four nat8) : Lemma
  (requires
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    x / 0x10000 == x' / 0x10000
  )
  (ensures t.hi3 == t'.hi3 /\ t.hi2 == t'.hi2)
  =
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  let t01 = t0 + 0x100 * t1 in
  let t23 = t2 + 0x100 * t3 in
  let t01' = t0' + 0x100 * t1' in
  let t23' = t2' + 0x100 * t3' in
  assert_norm (four_to_nat 8 t  == four_to_nat_unfold 8 t );
  assert_norm (four_to_nat 8 t' == four_to_nat_unfold 8 t');
  nat32_xor_bytewise_2_helper1 t23 t23' t01 t01' x x';
  ()

let nat32_xor_bytewise_3_helper2 (x x':nat32) (t t':four nat8) : Lemma
  (requires
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    x / 0x100 == x' / 0x100
  )
  (ensures t.hi3 == t'.hi3 /\ t.hi2 == t'.hi2 /\ t.lo1 == t'.lo1)
  =
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  let t123 = t1 + 0x100 * t2 + 0x10000 * t3 in
  let t123' = t1' + 0x100 * t2' + 0x10000 * t3' in
  assert_norm (four_to_nat 8 t  == four_to_nat_unfold 8 t );
  assert_norm (four_to_nat 8 t' == four_to_nat_unfold 8 t');
  nat32_xor_bytewise_3_helper1 t123 t123' t0 t0' x x';
  ()

let nat32_xor_bytewise_1_helper3 (k k':nat32) (s s':four nat8) : Lemma
  (requires
    k == four_to_nat 8 s /\
    k' == four_to_nat 8 s' /\
    s.hi3 == s'.hi3
  )
  (ensures k / 0x1000000 == k' / 0x1000000)
  =
  let Mkfour _ _ _ _ = s in
  let Mkfour _ _ _ _  = s' in
  assert_norm (four_to_nat 8 s  == four_to_nat_unfold 8 s );
  assert_norm (four_to_nat 8 s' == four_to_nat_unfold 8 s');
  ()

let nat32_xor_bytewise_2_helper3 (k k':nat32) (s s':four nat8) : Lemma
  (requires
    k == four_to_nat 8 s /\
    k' == four_to_nat 8 s' /\
    s.hi3 == s'.hi3 /\ s.hi2 == s'.hi2
  )
  (ensures k / 0x10000 == k' / 0x10000)
  =
  let Mkfour _ _ _ _ = s in
  let Mkfour _ _ _ _  = s' in
  assert_norm (four_to_nat 8 s  == four_to_nat_unfold 8 s );
  assert_norm (four_to_nat 8 s' == four_to_nat_unfold 8 s');
  ()

let nat32_xor_bytewise_3_helper3 (k k':nat32) (s s':four nat8) : Lemma
  (requires
    k == four_to_nat 8 s /\
    k' == four_to_nat 8 s' /\
    s.hi3 == s'.hi3 /\ s.hi2 == s'.hi2 /\ s.lo1 == s'.lo1
  )
  (ensures k / 0x100 == k' / 0x100)
  =
  let Mkfour _ _ _ _ = s in
  let Mkfour _ _ _ _  = s' in
  assert_norm (four_to_nat 8 s  == four_to_nat_unfold 8 s );
  assert_norm (four_to_nat 8 s' == four_to_nat_unfold 8 s');
  ()

let nat32_xor_bytewise_1 (k k' x x' m:nat32) (s s' t t':four nat8) : Lemma
  (requires
    k == four_to_nat 8 s /\
    k' == four_to_nat 8 s' /\
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    ixor k m == x /\
    ixor k' m == x' /\
    s.hi3 == s'.hi3
  )
  (ensures t.hi3 == t'.hi3)
  =
  let Mkfour s0 s1 s2 s3 = s in
  let Mkfour s0' s1' s2' s3' = s' in
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  nat32_xor_bytewise_1_helper3 k k' s s';
  lemma_ishr_32 k 24;
  lemma_ishr_32 k' 24;
  lemma_ishr_32 x 24;
  lemma_ishr_32 x' 24;
  lemma_ishr_ixor_32 k m 24;
  lemma_ishr_ixor_32 k' m 24;
  assert_norm (pow2 24 == pow2_24);
  nat32_xor_bytewise_1_helper2 x x' t t';
  ()

let nat32_xor_bytewise_2 (k k' x x' m:nat32) (s s' t t':four nat8) : Lemma
  (requires
    k == four_to_nat 8 s /\
    k' == four_to_nat 8 s' /\
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    ixor k m == x /\
    ixor k' m == x' /\
    s.hi3 == s'.hi3 /\ s.hi2 == s'.hi2
  )
  (ensures t.hi3 == t'.hi3 /\ t.hi2 == t'.hi2)
  =
  let Mkfour s0 s1 s2 s3 = s in
  let Mkfour s0' s1' s2' s3' = s' in
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  nat32_xor_bytewise_2_helper3 k k' s s';
  lemma_ishr_32 k 16;
  lemma_ishr_32 k' 16;
  lemma_ishr_32 x 16;
  lemma_ishr_32 x' 16;
  lemma_ishr_ixor_32 k m 16;
  lemma_ishr_ixor_32 k' m 16;
  nat32_xor_bytewise_2_helper2 x x' t t';
  ()

let nat32_xor_bytewise_3 (k k' x x' m:nat32) (s s' t t':four nat8) : Lemma
  (requires
    k == four_to_nat 8 s /\
    k' == four_to_nat 8 s' /\
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    ixor k m == x /\
    ixor k' m == x' /\
    s.hi3 == s'.hi3 /\ s.hi2 == s'.hi2 /\ s.lo1 == s'.lo1
  )
  (ensures t.hi3 == t'.hi3 /\ t.hi2 == t'.hi2 /\ t.lo1 == t'.lo1)
  =
  let Mkfour s0 s1 s2 s3 = s in
  let Mkfour s0' s1' s2' s3' = s' in
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  nat32_xor_bytewise_3_helper3 k k' s s';
  lemma_ishr_32 k 8;
  lemma_ishr_32 k' 8;
  lemma_ishr_32 x 8;
  lemma_ishr_32 x' 8;
  lemma_ishr_ixor_32 k m 8;
  lemma_ishr_ixor_32 k' m 8;
  nat32_xor_bytewise_3_helper2 x x' t t';
  ()

#reset-options "--z3rlimit 50 --smtencoding.nl_arith_repr boxwrap --smtencoding.l_arith_repr boxwrap"
let nat32_xor_bytewise_4 (k k' x x' m:nat32) (s s' t t':four nat8) : Lemma
  (requires
    k == four_to_nat 8 s /\
    k' == four_to_nat 8 s' /\
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    ixor k m == x /\
    ixor k' m == x' /\
    s == s'
  )
  (ensures t == t')
  =
  let Mkfour s0 s1 s2 s3 = s in
  let Mkfour s0' s1' s2' s3' = s' in
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  assert_norm (four_to_nat 8 t' == four_to_nat_unfold 8 t');
  assert_norm (four_to_nat 8 t  == four_to_nat_unfold 8 t );
  ()
#reset-options

let nat32_xor_bytewise (k k' m:nat32) (s s' t t':seq4 nat8) (n:nat) : Lemma
  (requires
    n <= 4 /\
    k == four_to_nat 8 (seq_to_four_BE s) /\
    k' == four_to_nat 8 (seq_to_four_BE s') /\
    ixor k m == four_to_nat 8 (seq_to_four_BE t) /\
    ixor k' m == four_to_nat 8 (seq_to_four_BE t') /\
    equal (slice s 0 n) (slice s' 0 n)
  )
  (ensures (forall (i:nat).{:pattern (index t i) \/ (index t' i)} i < n ==> index t i == index t' i))
  =
  assert (n > 0 ==> index (slice s 0 n) 0 == index (slice s' 0 n) 0);
  assert (n > 1 ==> index (slice s 0 n) 1 == index (slice s' 0 n) 1);
  assert (n > 2 ==> index (slice s 0 n) 2 == index (slice s' 0 n) 2);
  assert (n > 3 ==> index (slice s 0 n) 3 == index (slice s' 0 n) 3);
  let x = ixor k m in
  let x' = ixor k' m in
  if n = 1 then nat32_xor_bytewise_1 k k' x x' m (seq_to_four_BE s) (seq_to_four_BE s') (seq_to_four_BE t) (seq_to_four_BE t');
  if n = 2 then nat32_xor_bytewise_2 k k' x x' m (seq_to_four_BE s) (seq_to_four_BE s') (seq_to_four_BE t) (seq_to_four_BE t');
  if n = 3 then nat32_xor_bytewise_3 k k' x x' m (seq_to_four_BE s) (seq_to_four_BE s') (seq_to_four_BE t) (seq_to_four_BE t');
  if n = 4 then nat32_xor_bytewise_4 k k' x x' m (seq_to_four_BE s) (seq_to_four_BE s') (seq_to_four_BE t) (seq_to_four_BE t');
  assert (equal (slice t 0 n) (slice t' 0 n));
  lemma_slice_orig_index t t' 0 n;
  ()

let quad32_xor_bytewise (q q' r:quad32) (n:nat{ n <= 16 }) : Lemma
  (requires (let q_bytes  = be_quad32_to_bytes q in
             let q'_bytes = be_quad32_to_bytes q' in
             slice q_bytes 0 n == slice q'_bytes 0 n))
  (ensures (let q_bytes  = be_quad32_to_bytes q in
            let q'_bytes = be_quad32_to_bytes q' in
            let qr_bytes  = be_quad32_to_bytes (quad32_xor q r) in
            let q'r_bytes = be_quad32_to_bytes (quad32_xor q' r) in
            slice qr_bytes 0 n == slice q'r_bytes 0 n))
  =
  let s = be_quad32_to_bytes q in
  let s' = be_quad32_to_bytes q' in
  let t = be_quad32_to_bytes (quad32_xor q r) in
  let t' = be_quad32_to_bytes (quad32_xor q' r) in
  lemma_slices_be_quad32_to_bytes q;
  lemma_slices_be_quad32_to_bytes q';
  lemma_slices_be_quad32_to_bytes (quad32_xor q r);
  lemma_slices_be_quad32_to_bytes (quad32_xor q' r);
  lemma_slice_orig_index s s' 0 n;
  quad32_xor_reveal ();
  if n < 4 then nat32_xor_bytewise q.hi3 q'.hi3 r.hi3 (slice s 0 4) (slice s' 0 4) (slice t 0 4) (slice t' 0 4) n
  else
  (
    nat32_xor_bytewise q.hi3 q'.hi3 r.hi3 (slice s 0 4) (slice s' 0 4) (slice t 0 4) (slice t' 0 4) 4;
    if n < 8 then nat32_xor_bytewise q.hi2 q'.hi2 r.hi2 (slice s 4 8) (slice s' 4 8) (slice t 4 8) (slice t' 4 8) (n - 4)
    else
    (
      nat32_xor_bytewise q.hi2 q'.hi2 r.hi2 (slice s 4 8) (slice s' 4 8) (slice t 4 8) (slice t' 4 8) 4;
      if n < 12 then nat32_xor_bytewise q.lo1 q'.lo1 r.lo1 (slice s 8 12) (slice s' 8 12) (slice t 8 12) (slice t' 8 12) (n - 8)
      else
      (
        nat32_xor_bytewise q.lo1 q'.lo1 r.lo1 (slice s 8 12) (slice s' 8 12) (slice t 8 12) (slice t' 8 12) 4;
        nat32_xor_bytewise q.lo0 q'.lo0 r.lo0 (slice s 12 16) (slice s' 12 16) (slice t 12 16) (slice t' 12 16) (n - 12);
        ()
      )
    )
  );
  assert (equal (slice t 0 n) (slice t' 0 n));
  ()

let slice_pad_to_128_bits (s:seq nat8 {  0 < length s /\ length s < 16 }) :
  Lemma(slice (pad_to_128_bits s) 0 (length s) == s)
  =
  assert (length s % 16 == length s);
  assert (equal s (slice (pad_to_128_bits s) 0 (length s)));
  ()

let step2 (s:seq nat8 {  0 < length s /\ length s < 16 }) (q:quad32) (icb_BE:quad32) (alg:algorithm) (key:aes_key_word alg) (i:int):
  Lemma(let q_bytes = be_quad32_to_bytes q in
        let q_bytes_prefix = slice q_bytes 0 (length s) in
        let q_cipher = gctr_encrypt_block icb_BE q alg key i in
        let q_cipher_bytes = slice (be_quad32_to_bytes q_cipher) 0 (length s) in
        let s_quad = be_bytes_to_quad32 (pad_to_128_bits s) in
        let s_cipher = gctr_encrypt_block icb_BE s_quad alg key i in
        let s_cipher_bytes = slice (be_quad32_to_bytes s_cipher) 0 (length s) in
        s == q_bytes_prefix ==> s_cipher_bytes == q_cipher_bytes)
  =
  let q_bytes = be_quad32_to_bytes q in
  let q_bytes_prefix = slice q_bytes 0 (length s) in
  let q_cipher = gctr_encrypt_block icb_BE q alg key i in
  let q_cipher_bytes = slice (be_quad32_to_bytes q_cipher) 0 (length s) in
  let s_quad = be_bytes_to_quad32 (pad_to_128_bits s) in
  let s_cipher = gctr_encrypt_block icb_BE s_quad alg key i in
  let s_cipher_bytes = slice (be_quad32_to_bytes s_cipher) 0 (length s) in
  let enc_ctr = aes_encrypt_word alg key (inc32 icb_BE i) in
  let icb = inc32 icb_BE i in

  if s = q_bytes_prefix then (
    be_quad32_to_bytes_to_quad32 (pad_to_128_bits s);
    slice_pad_to_128_bits s;
    quad32_xor_bytewise q (be_bytes_to_quad32 (pad_to_128_bits s)) (aes_encrypt_word alg key icb) (length s);
    ()
  ) else
    ();
  ()

#reset-options "--z3rlimit 30"
open FStar.Seq.Properties

let gctr_partial_to_full_advanced (icb_BE:quad32) (plain:seq quad32) (cipher:seq quad32) (alg:algorithm) (key:seq nat32) (num_bytes:nat) =
  gctr_encrypt_reveal ();
  let num_blocks = num_bytes / 16 in
  let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) 0 num_bytes in
  let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 num_bytes in
  step1 plain num_bytes;
  let s = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) (num_blocks * 16) num_bytes in
  let final_p = index plain num_blocks in
  step2 s final_p icb_BE alg key num_blocks;

  let num_extra = num_bytes % 16 in
  let full_bytes_len = num_bytes - num_extra in
  let full_blocks, final_block = split plain_bytes full_bytes_len in
  assert (full_bytes_len % 16 == 0);
  assert (length full_blocks == full_bytes_len);
  let full_quads_BE = be_bytes_to_seq_quad32 full_blocks in
  let final_quad_BE = be_bytes_to_quad32 (pad_to_128_bits final_block) in
  let cipher_quads_BE = gctr_encrypt_recursive icb_BE full_quads_BE alg key 0 in
  let final_cipher_quad_BE = gctr_encrypt_block icb_BE final_quad_BE alg key (full_bytes_len / 16) in
  assert (cipher_quads_BE == slice cipher 0 num_blocks);   // LHS quads
  let cipher_bytes_full_BE = seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_quads_BE) in
  let final_cipher_bytes_BE = slice (be_quad32_to_bytes final_cipher_quad_BE) 0 num_extra in

  assert (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_quads_BE) == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice cipher 0 num_blocks))); // LHS bytes

  assert (length s == num_extra);
  let q_prefix = slice (be_quad32_to_bytes final_p) 0 num_extra in
  be_seq_quad32_to_bytes_tail_prefix plain num_bytes;
  assert (q_prefix == s);

  assert(final_cipher_bytes_BE == slice (be_quad32_to_bytes (index cipher num_blocks)) 0 num_extra); // RHS bytes

  be_seq_quad32_to_bytes_tail_prefix cipher num_bytes;
  assert (slice (be_quad32_to_bytes (index cipher num_blocks)) 0 num_extra ==
          slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) (num_blocks * 16) num_bytes);

  slice_commutes_be_seq_quad32_to_bytes0 cipher num_blocks;
  assert (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice cipher 0 num_blocks)) == slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 (num_blocks * 16));


  assert (slice (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) (num_blocks * 16) (length cipher * 16)) 0 num_extra ==
          slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) (num_blocks * 16) num_bytes);
  slice_append_adds (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) (num_blocks * 16) num_bytes;
  assert (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 (num_blocks * 16) @|
          slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) (num_blocks * 16) num_bytes ==
          slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 num_bytes);
  assert (cipher_bytes == (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice cipher 0 num_blocks))) @| slice (be_quad32_to_bytes (index cipher num_blocks)) 0 num_extra);
  ()

let gctr_encrypt_one_block (icb plain:quad32) (alg:algorithm) (key:seq nat32) =
  gctr_encrypt_reveal ();
  assert(inc32 icb 0 == icb);
  let encrypted_icb = aes_encrypt_word alg key icb in
  let p = be_quad32_to_bytes plain in
  let plain_quads = be_bytes_to_seq_quad32 p in
  let p_seq = create 1 plain in
  assert (length p == 16);
  be_bytes_to_seq_quad32_to_bytes_one_quad plain;
  assert (p_seq == plain_quads);
  let cipher_quads = gctr_encrypt_recursive icb plain_quads alg key 0 in
  assert (cipher_quads == cons (gctr_encrypt_block icb (head plain_quads) alg key 0) (gctr_encrypt_recursive icb (tail plain_quads) alg key (1)));
  assert (head plain_quads == plain);

  assert (gctr_encrypt_block icb (head plain_quads) alg key 0 ==
          (quad32_xor (head plain_quads) (aes_encrypt_word alg key icb)));
  assert (quad32_xor plain (aes_encrypt_word alg key icb)
          ==
          (quad32_xor (head plain_quads) (aes_encrypt_word alg key (inc32 icb 0))));
  assert (gctr_encrypt_block icb (head plain_quads) alg key 0 == quad32_xor plain (aes_encrypt_word alg key icb));
  aes_encrypt_word_reveal ();
  assert (gctr_encrypt_block icb (head plain_quads) alg key 0 == quad32_xor plain (aes_encrypt_word alg key icb));
  assert (gctr_encrypt_block icb (head plain_quads) alg key 0 == quad32_xor plain encrypted_icb);
  assert(gctr_encrypt_recursive icb (tail p_seq) alg key 1 == empty);   // OBSERVE
  let x = quad32_xor plain encrypted_icb in
  append_empty_r (create 1 x);
  ()
