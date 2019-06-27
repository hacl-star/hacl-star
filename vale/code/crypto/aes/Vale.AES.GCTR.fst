module Vale.AES.GCTR

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open FStar.Seq
open Vale.AES.AES_s
open Vale.AES.GCTR_s
open Vale.AES.GCM_helpers
open FStar.Math.Lemmas
open Vale.Lib.Seqs

#set-options "--z3rlimit 20 --max_fuel 1 --max_ifuel 0"

let gctr_encrypt_block_offset (icb_BE:quad32) (plain_LE:quad32) (alg:algorithm) (key:seq nat32) (i:int) =
  ()

let gctr_encrypt_empty (icb_BE:quad32) (plain_LE cipher_LE:seq quad32) (alg:algorithm) (key:seq nat32) =
  FStar.Pervasives.reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32;
  reveal_opaque gctr_encrypt_LE_def;
  let plain = slice (le_seq_quad32_to_bytes plain_LE) 0 0 in
  let cipher = slice (le_seq_quad32_to_bytes cipher_LE) 0 0 in
  assert (plain == empty);
  assert (cipher == empty);
  assert (length plain == 0);
  assert (make_gctr_plain_LE plain == empty);
  let num_extra = (length (make_gctr_plain_LE plain)) % 16 in
  assert (num_extra == 0);
  let plain_quads_LE = le_bytes_to_seq_quad32 plain in
  let cipher_quads_LE = gctr_encrypt_recursive icb_BE plain_quads_LE alg key 0 in
  assert (equal plain_quads_LE empty);     // OBSERVE
  assert (plain_quads_LE == empty);
  assert (cipher_quads_LE == empty);
  assert (equal (le_seq_quad32_to_bytes cipher_quads_LE) empty);  // OBSERVEs
  ()

let gctr_partial_extend6 (alg:algorithm) (bound:nat) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32)
  =
  reveal_opaque gctr_partial;
  ()

(*
let rec seq_map_i_indexed' (#a:Type) (#b:Type) (f:int->a->b) (s:seq a) (i:int) :
  Tot (s':seq b { length s' == length s /\
                  (forall j . {:pattern index s' j} 0 <= j /\ j < length s ==> index s' j == f (i + j) (index s j))
                })
      (decreases (length s))
  =
  if length s = 0 then empty
  else cons (f i (head s)) (seq_map_i_indexed f (tail s) (i + 1))

let rec test (icb_BE:quad32) (plain_LE:gctr_plain_internal_LE)
         (alg:algorithm) (key:aes_key_LE alg) (i:int) :
  Lemma (ensures
     (let gctr_encrypt_block_curried (j:int) (p:quad32) = gctr_encrypt_block icb_BE p alg key j in

      gctr_encrypt_recursive icb_BE plain_LE alg key i == seq_map_i_indexed' gctr_encrypt_block_curried plain_LE i))
     (decreases (length plain_LE))
  =
  let gctr_encrypt_block_curried (j:int) (p:quad32) = gctr_encrypt_block icb_BE p alg key j in
  let g = gctr_encrypt_recursive icb_BE plain_LE alg key i in
  let s = seq_map_i_indexed' gctr_encrypt_block_curried plain_LE i in
  if length plain_LE = 0 then (
    assert(equal (g) (s));
    ()
  ) else (
    test icb_BE (tail plain_LE) alg key (i+1);
    assert (gctr_encrypt_recursive icb_BE (tail plain_LE) alg key (i+1) == seq_map_i_indexed' gctr_encrypt_block_curried (tail plain_LE) (i+1))
  )
*)

let rec gctr_encrypt_recursive_length (icb:quad32) (plain:gctr_plain_internal_LE)
                                      (alg:algorithm) (key:aes_key_LE alg) (i:int) : Lemma
  (requires True)
  (ensures length (gctr_encrypt_recursive icb plain alg key i) == length plain)
  (decreases %[length plain])
  [SMTPat (length (gctr_encrypt_recursive icb plain alg key i))]
  =
  if length plain = 0 then ()
  else gctr_encrypt_recursive_length icb (tail plain) alg key (i + 1)

#reset-options "--z3rlimit 40"
let rec gctr_encrypt_length (icb_BE:quad32) (plain:gctr_plain_LE)
                             (alg:algorithm) (key:aes_key_LE alg) :
  Lemma(length (gctr_encrypt_LE icb_BE plain alg key) == length plain)
  [SMTPat (length (gctr_encrypt_LE icb_BE plain alg key))]
  =
  FStar.Pervasives.reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32;
  reveal_opaque gctr_encrypt_LE_def;
  let num_extra = (length plain) % 16 in
  let result = gctr_encrypt_LE icb_BE plain alg key in
  if num_extra = 0 then (
    let plain_quads_LE = le_bytes_to_seq_quad32 plain in
    gctr_encrypt_recursive_length icb_BE plain_quads_LE alg key 0
  ) else (
    let full_bytes_len = (length plain) - num_extra in
    let full_blocks, final_block = split plain full_bytes_len in

    let full_quads_LE = le_bytes_to_seq_quad32 full_blocks in
    let final_quad_LE = le_bytes_to_quad32 (pad_to_128_bits final_block) in

    let cipher_quads_LE = gctr_encrypt_recursive icb_BE full_quads_LE alg key 0 in
    let final_cipher_quad_LE = gctr_encrypt_block icb_BE final_quad_LE alg key (full_bytes_len / 16) in

    let cipher_bytes_full_LE = le_seq_quad32_to_bytes cipher_quads_LE in
    let final_cipher_bytes_LE = slice (le_quad32_to_bytes final_cipher_quad_LE) 0 num_extra in

    gctr_encrypt_recursive_length icb_BE full_quads_LE alg key 0;
    assert (length result == length cipher_bytes_full_LE + length final_cipher_bytes_LE);
    assert (length cipher_quads_LE == length full_quads_LE);
    assert (length cipher_bytes_full_LE == 16 * length cipher_quads_LE);
    assert (16 * length full_quads_LE == length full_blocks);
    assert (length cipher_bytes_full_LE == length full_blocks);
    ()
  )
#reset-options

//#reset-options "--use_two_phase_tc true" // Needed so that indexing cipher and plain knows that their lengths are equal
let rec gctr_indexed_helper (icb:quad32) (plain:gctr_plain_internal_LE)
                            (alg:algorithm) (key:aes_key_LE alg) (i:int) : Lemma
  (requires True)
  (ensures (let cipher = gctr_encrypt_recursive icb plain alg key i in
            length cipher == length plain /\
           (forall j . {:pattern index cipher j} 0 <= j /\ j < length plain ==>
           index cipher j == quad32_xor (index plain j) (aes_encrypt_BE alg key (inc32 icb (i + j)) ))))
  (decreases %[length plain])
=
  if length plain = 0 then ()
  else
      let tl = tail plain in
      let cipher = gctr_encrypt_recursive icb plain alg key i in
      let r_cipher = gctr_encrypt_recursive icb tl alg key (i+1) in
      let helper (j:int) :
        Lemma ((0 <= j /\ j < length plain) ==> (index cipher j == quad32_xor (index plain j) (aes_encrypt_BE alg key (inc32 icb (i + j)) )))
        =
        FStar.Pervasives.reveal_opaque (`%aes_encrypt_le) aes_encrypt_le;
        if 0 < j && j < length plain then (
          gctr_indexed_helper icb tl alg key (i+1);
          assert(index r_cipher (j-1) == quad32_xor (index tl (j-1)) (aes_encrypt_BE alg key (inc32 icb (i + 1 + j - 1)) )) // OBSERVE
        ) else ()
      in
      FStar.Classical.forall_intro helper

let rec gctr_indexed (icb:quad32) (plain:gctr_plain_internal_LE)
                     (alg:algorithm) (key:aes_key_LE alg) (cipher:seq quad32) : Lemma
  (requires  length cipher == length plain /\
             (forall i . {:pattern index cipher i} 0 <= i /\ i < length cipher ==>
             index cipher i == quad32_xor (index plain i) (aes_encrypt_BE alg key (inc32 icb i) )))
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
    is_aes_key_LE alg key /\
    length plain == length cipher /\
    length plain < pow2_32 /\
    gctr_partial_opaque alg (length cipher) plain cipher key icb
  )
  (ensures cipher == gctr_encrypt_recursive icb plain alg key 0)
  =
  reveal_opaque gctr_partial;
  gctr_partial_completed alg plain cipher key icb

let gctr_partial_to_full_basic (icb_BE:quad32) (plain:seq quad32) (alg:algorithm) (key:seq nat32) (cipher:seq quad32) =
  reveal_opaque gctr_encrypt_LE_def;
  let p = le_seq_quad32_to_bytes plain in
  assert (length p % 16 == 0);
  let plain_quads_LE = le_bytes_to_seq_quad32 p in
  let cipher_quads_LE = gctr_encrypt_recursive icb_BE plain_quads_LE alg key 0 in
  let cipher_bytes = le_seq_quad32_to_bytes cipher_quads_LE in
  le_bytes_to_seq_quad32_to_bytes plain;
  ()


(*
Want to show that:
   slice (le_seq_quad32_to_bytes (buffer128_as_seq(mem, out_b))) 0 num_bytes
   ==
   gctr_encrypt_LE icb_BE (slice (le_seq_quad32_to_bytes (buffer128_as_seq(mem, in_b))) 0 num_bytes) ...

We know that
   slice (buffer128_as_seq(mem, out_b) 0 num_blocks
   ==
   gctr_encrypt_recursive icb_BE (slice buffer128_as_seq(mem, in_b) 0 num_blocks) ...

And we know that:
  get_mem out_b num_blocks
  ==
  gctr_encrypt_block(icb_BE, (get_mem inb num_blocks), alg, key, num_blocks);


Internally gctr_encrypt_LE will compute:
  full_blocks, final_block = split (slice (le_seq_quad32_to_bytes (buffer128_as_seq(mem, in_b))) 0 num_bytes) (num_blocks * 16)

  We'd like to show that
  Step1:  le_bytes_to_seq_quad32 full_blocks == slice buffer128_as_seq(mem, in_b) 0 num_blocks
    and
  Step2:  final_block == slice (le_quad32_to_bytes (get_mem inb num_blocks)) 0 num_extra

  Then we need to break down the byte-level effects of gctr_encrypt_block to show that even though the
  padded version of final_block differs from (get_mem inb num_blocks), after we slice it at the end,
  we end up with the same value
*)


let step1 (p:seq quad32) (num_bytes:nat{ num_bytes < 16 * length p }) : Lemma
  (let num_extra = num_bytes % 16 in
   let num_blocks = num_bytes / 16 in
   let full_blocks, final_block = split (slice (le_seq_quad32_to_bytes p) 0 num_bytes) (num_blocks * 16) in
   let full_quads_LE = le_bytes_to_seq_quad32 full_blocks in
   let p_prefix = slice p 0 num_blocks in
   p_prefix == full_quads_LE)
  =
  let num_extra = num_bytes % 16 in
  let num_blocks = num_bytes / 16 in
  let full_blocks, final_block = split (slice (le_seq_quad32_to_bytes p) 0 num_bytes) (num_blocks * 16) in
  let full_quads_LE = le_bytes_to_seq_quad32 full_blocks in
  let p_prefix = slice p 0 num_blocks in
  assert (length full_blocks == num_blocks * 16);
  assert (full_blocks == slice (slice (le_seq_quad32_to_bytes p) 0 num_bytes) 0 (num_blocks * 16));
  assert (full_blocks == slice (le_seq_quad32_to_bytes p) 0 (num_blocks * 16));
  slice_commutes_le_seq_quad32_to_bytes0 p num_blocks;
  assert (full_blocks == le_seq_quad32_to_bytes (slice p 0 num_blocks));
  le_bytes_to_seq_quad32_to_bytes (slice p 0 num_blocks);
  assert (full_quads_LE == (slice p 0 num_blocks));
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

let lemma_ishl_32 (x:nat32) (k:nat) : Lemma
  (ensures ishl #pow2_32 x k == x * pow2 k % pow2_32)
  =
  Vale.Def.TypesNative_s.reveal_ishl 32 x k;
  FStar.UInt.shift_left_value_lemma #32 x k;
  ()

let lemma_ishl_ixor_32 (x y:nat32) (k:nat) : Lemma
  (ensures ishl #pow2_32 (ixor x y) k == ixor (ishl x k) (ishl y k))
  =
  Vale.Def.TypesNative_s.reveal_ishl 32 x k;
  Vale.Def.TypesNative_s.reveal_ishl 32 y k;
  Vale.Def.TypesNative_s.reveal_ishl 32 (ixor x y) k;
  Vale.Def.TypesNative_s.reveal_ixor 32 x y;
  Vale.Def.TypesNative_s.reveal_ixor 32 (ishl x k) (ishl y k);
  FStar.UInt.shift_left_logxor_lemma #32 x y k;
  ()

unfold let pow2_24 = 0x1000000
let nat24 = natN pow2_24

let nat32_xor_bytewise_1_helper1 (x0 x0':nat8) (x1 x1':nat24) (x x':nat32) : Lemma
  (requires
    x == x0 + 0x100 * x1 /\
    x' == x0' + 0x100 * x1' /\
    x * 0x1000000 % 0x100000000 == x' * 0x1000000 % 0x100000000
  )
  (ensures x0 == x0')
  =
  ()

let nat32_xor_bytewise_2_helper1 (x0 x0' x1 x1':nat16) (x x':nat32) : Lemma
  (requires
    x == x0 + 0x10000 * x1 /\
    x' == x0' + 0x10000 * x1' /\
    x * 0x10000 % 0x100000000 == x' * 0x10000 % 0x100000000
  )
  (ensures x0 == x0')
  =
  ()

let nat32_xor_bytewise_3_helper1 (x0 x0':nat24) (x1 x1':nat8) (x x':nat32) : Lemma
  (requires
    x == x0 + 0x1000000 * x1 /\
    x' == x0' + 0x1000000 * x1' /\
    x * 0x100 % 0x100000000 == x' * 0x100 % 0x100000000
  )
  (ensures x0 == x0')
  =
  ()

let nat32_xor_bytewise_1_helper2 (x x':nat32) (t t':four nat8) : Lemma
  (requires
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    x * 0x1000000 % 0x100000000 == x' * 0x1000000 % 0x100000000
  )
  (ensures t.lo0 == t'.lo0)
  =
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  let t123 = t1 + 0x100 * t2 + 0x10000 * t3 in
  let t123' = t1' + 0x100 * t2' + 0x10000 * t3' in
  assert_norm (four_to_nat 8 t  == four_to_nat_unfold 8 t );
  assert_norm (four_to_nat 8 t' == four_to_nat_unfold 8 t');
  nat32_xor_bytewise_1_helper1 t0 t0' t123 t123' x x';
  ()

let nat32_xor_bytewise_2_helper2 (x x':nat32) (t t':four nat8) : Lemma
  (requires
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    x * 0x10000 % 0x100000000 == x' * 0x10000 % 0x100000000
  )
  (ensures t.lo0 == t'.lo0 /\ t.lo1 == t'.lo1)
  =
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  let t01 = t0 + 0x100 * t1 in
  let t23 = t2 + 0x100 * t3 in
  let t01' = t0' + 0x100 * t1' in
  let t23' = t2' + 0x100 * t3' in
  assert_norm (four_to_nat 8 t  == four_to_nat_unfold 8 t );
  assert_norm (four_to_nat 8 t' == four_to_nat_unfold 8 t');
  nat32_xor_bytewise_2_helper1 t01 t01' t23 t23' x x';
  ()

let nat32_xor_bytewise_3_helper2 (x x':nat32) (t t':four nat8) : Lemma
  (requires
    x == four_to_nat 8 t /\
    x' == four_to_nat 8 t' /\
    x * 0x100 % 0x100000000 == x' * 0x100 % 0x100000000
  )
  (ensures t.lo0 == t'.lo0 /\ t.lo1 == t'.lo1 /\ t.hi2 == t'.hi2)
  =
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  let t012 = t0 + 0x100 * t1 + 0x10000 * t2 in
  let t012' = t0' + 0x100 * t1' + 0x10000 * t2' in
  assert_norm (four_to_nat 8 t  == four_to_nat_unfold 8 t );
  assert_norm (four_to_nat 8 t' == four_to_nat_unfold 8 t');
  nat32_xor_bytewise_3_helper1 t012 t012' t3 t3' x x';
  ()

let nat32_xor_bytewise_1_helper3 (k k':nat32) (s s':four nat8) : Lemma
  (requires
    k == four_to_nat 8 s /\
    k' == four_to_nat 8 s' /\
    s.lo0 == s'.lo0
  )
  (ensures k * 0x1000000 % 0x100000000 == k' * 0x1000000 % 0x100000000)
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
    s.lo0 == s'.lo0 /\ s.lo1 == s'.lo1
  )
  (ensures k * 0x10000 % 0x100000000 == k' * 0x10000 % 0x100000000)
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
    s.lo0 == s'.lo0 /\ s.lo1 == s'.lo1 /\ s.hi2 == s'.hi2
  )
  (ensures k * 0x100 % 0x100000000 == k' * 0x100 % 0x100000000)
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
    s.lo0 == s'.lo0
  )
  (ensures t.lo0 == t'.lo0)
  =
  let Mkfour s0 s1 s2 s3 = s in
  let Mkfour s0' s1' s2' s3' = s' in
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  nat32_xor_bytewise_1_helper3 k k' s s';
  lemma_ishl_32 k 24;
  lemma_ishl_32 k' 24;
  lemma_ishl_32 x 24;
  lemma_ishl_32 x' 24;
  lemma_ishl_ixor_32 k m 24;
  lemma_ishl_ixor_32 k' m 24;
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
    s.lo0 == s'.lo0 /\ s.lo1 == s'.lo1
  )
  (ensures t.lo0 == t'.lo0 /\ t.lo1 == t'.lo1)
  =
  let Mkfour s0 s1 s2 s3 = s in
  let Mkfour s0' s1' s2' s3' = s' in
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  nat32_xor_bytewise_2_helper3 k k' s s';
  lemma_ishl_32 k 16;
  lemma_ishl_32 k' 16;
  lemma_ishl_32 x 16;
  lemma_ishl_32 x' 16;
  lemma_ishl_ixor_32 k m 16;
  lemma_ishl_ixor_32 k' m 16;
//  assert (ishl #pow2_32 k  16 == k  * 0x10000 % 0x100000000);
//  assert (ishl #pow2_32 k' 16 == k' * 0x10000 % 0x100000000);
//  assert (ishl #pow2_32 x  16 == x  * 0x10000 % 0x100000000);
//  assert (ishl #pow2_32 x' 16 == x' * 0x10000 % 0x100000000);
//  assert (ishl #pow2_32 x  16 == ixor (ishl k  16) (ishl m 16));
//  assert (ishl #pow2_32 x' 16 == ixor (ishl k' 16) (ishl m 16));
//  assert (x  * 0x10000 % 0x100000000 == ixor (k  * 0x10000 % 0x100000000) (ishl m 16));
//  assert (x' * 0x10000 % 0x100000000 == ixor (k' * 0x10000 % 0x100000000) (ishl m 16));
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
    s.lo0 == s'.lo0 /\ s.lo1 == s'.lo1 /\ s.hi2 == s'.hi2
  )
  (ensures t.lo0 == t'.lo0 /\ t.lo1 == t'.lo1 /\ t.hi2 == t'.hi2)
  =
  let Mkfour s0 s1 s2 s3 = s in
  let Mkfour s0' s1' s2' s3' = s' in
  let Mkfour t0 t1 t2 t3 = t in
  let Mkfour t0' t1' t2' t3' = t' in
  nat32_xor_bytewise_3_helper3 k k' s s';
  lemma_ishl_32 k 8;
  lemma_ishl_32 k' 8;
  lemma_ishl_32 x 8;
  lemma_ishl_32 x' 8;
  lemma_ishl_ixor_32 k m 8;
  lemma_ishl_ixor_32 k' m 8;
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
    k == four_to_nat 8 (seq_to_four_LE s) /\
    k' == four_to_nat 8 (seq_to_four_LE s') /\
    ixor k m == four_to_nat 8 (seq_to_four_LE t) /\
    ixor k' m == four_to_nat 8 (seq_to_four_LE t') /\
    equal (slice s 0 n) (slice s' 0 n)
  )
//  (ensures equal (slice t 0 n) (slice t' 0 n))
  (ensures (forall (i:nat).{:pattern (index t i) \/ (index t' i)} i < n ==> index t i == index t' i))
  =
  assert (n > 0 ==> index (slice s 0 n) 0 == index (slice s' 0 n) 0);
  assert (n > 1 ==> index (slice s 0 n) 1 == index (slice s' 0 n) 1);
  assert (n > 2 ==> index (slice s 0 n) 2 == index (slice s' 0 n) 2);
  assert (n > 3 ==> index (slice s 0 n) 3 == index (slice s' 0 n) 3);
  let x = ixor k m in
  let x' = ixor k' m in
  if n = 1 then nat32_xor_bytewise_1 k k' x x' m (seq_to_four_LE s) (seq_to_four_LE s') (seq_to_four_LE t) (seq_to_four_LE t');
  if n = 2 then nat32_xor_bytewise_2 k k' x x' m (seq_to_four_LE s) (seq_to_four_LE s') (seq_to_four_LE t) (seq_to_four_LE t');
  if n = 3 then nat32_xor_bytewise_3 k k' x x' m (seq_to_four_LE s) (seq_to_four_LE s') (seq_to_four_LE t) (seq_to_four_LE t');
  if n = 4 then nat32_xor_bytewise_4 k k' x x' m (seq_to_four_LE s) (seq_to_four_LE s') (seq_to_four_LE t) (seq_to_four_LE t');
  assert (equal (slice t 0 n) (slice t' 0 n));
  lemma_slice_orig_index t t' 0 n;
  ()

// REVIEW: should be shared with GCM_helpers
let lemma_slices_le_quad32_to_bytes (q:quad32) : Lemma
  (ensures (
    let s = le_quad32_to_bytes q in
    q.lo0 == four_to_nat 8 (seq_to_four_LE (slice s 0 4)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_LE (slice s 4 8)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_LE (slice s 8 12)) /\
    q.hi3 == four_to_nat 8 (seq_to_four_LE (slice s 12 16))
  ))
  =
  FStar.Pervasives.reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat8);
  FStar.Pervasives.reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes;
  ()

let quad32_xor_bytewise (q q' r:quad32) (n:nat{ n <= 16 }) : Lemma
  (requires (let q_bytes  = le_quad32_to_bytes q in
             let q'_bytes = le_quad32_to_bytes q' in
             slice q_bytes 0 n == slice q'_bytes 0 n))
  (ensures (let q_bytes  = le_quad32_to_bytes q in
            let q'_bytes = le_quad32_to_bytes q' in
            let qr_bytes  = le_quad32_to_bytes (quad32_xor q r) in
            let q'r_bytes = le_quad32_to_bytes (quad32_xor q' r) in
            slice qr_bytes 0 n == slice q'r_bytes 0 n))
  =
  let s = le_quad32_to_bytes q in
  let s' = le_quad32_to_bytes q' in
  let t = le_quad32_to_bytes (quad32_xor q r) in
  let t' = le_quad32_to_bytes (quad32_xor q' r) in
  lemma_slices_le_quad32_to_bytes q;
  lemma_slices_le_quad32_to_bytes q';
  lemma_slices_le_quad32_to_bytes (quad32_xor q r);
  lemma_slices_le_quad32_to_bytes (quad32_xor q' r);
  lemma_slice_orig_index s s' 0 n;
  reveal_opaque quad32_xor_def;
  reveal_opaque reverse_bytes_nat32_def;
  if n < 4 then nat32_xor_bytewise q.lo0 q'.lo0 r.lo0 (slice s 0 4) (slice s' 0 4) (slice t 0 4) (slice t' 0 4) n
  else
  (
    nat32_xor_bytewise q.lo0 q'.lo0 r.lo0 (slice s 0 4) (slice s' 0 4) (slice t 0 4) (slice t' 0 4) 4;
    if n < 8 then nat32_xor_bytewise q.lo1 q'.lo1 r.lo1 (slice s 4 8) (slice s' 4 8) (slice t 4 8) (slice t' 4 8) (n - 4)
    else
    (
      nat32_xor_bytewise q.lo1 q'.lo1 r.lo1 (slice s 4 8) (slice s' 4 8) (slice t 4 8) (slice t' 4 8) 4;
      if n < 12 then nat32_xor_bytewise q.hi2 q'.hi2 r.hi2 (slice s 8 12) (slice s' 8 12) (slice t 8 12) (slice t' 8 12) (n - 8)
      else
      (
        nat32_xor_bytewise q.hi2 q'.hi2 r.hi2 (slice s 8 12) (slice s' 8 12) (slice t 8 12) (slice t' 8 12) 4;
        nat32_xor_bytewise q.hi3 q'.hi3 r.hi3 (slice s 12 16) (slice s' 12 16) (slice t 12 16) (slice t' 12 16) (n - 12);
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

let step2 (s:seq nat8 {  0 < length s /\ length s < 16 }) (q:quad32) (icb_BE:quad32) (alg:algorithm) (key:aes_key_LE alg) (i:int):
  Lemma(let q_bytes = le_quad32_to_bytes q in
        let q_bytes_prefix = slice q_bytes 0 (length s) in
        let q_cipher = gctr_encrypt_block icb_BE q alg key i in
        let q_cipher_bytes = slice (le_quad32_to_bytes q_cipher) 0 (length s) in
        let s_quad = le_bytes_to_quad32 (pad_to_128_bits s) in
        let s_cipher = gctr_encrypt_block icb_BE s_quad alg key i in
        let s_cipher_bytes = slice (le_quad32_to_bytes s_cipher) 0 (length s) in
        s == q_bytes_prefix ==> s_cipher_bytes == q_cipher_bytes)
  =
  let q_bytes = le_quad32_to_bytes q in
  let q_bytes_prefix = slice q_bytes 0 (length s) in
  let q_cipher = gctr_encrypt_block icb_BE q alg key i in
  let q_cipher_bytes = slice (le_quad32_to_bytes q_cipher) 0 (length s) in
  let s_quad = le_bytes_to_quad32 (pad_to_128_bits s) in
  let s_cipher = gctr_encrypt_block icb_BE s_quad alg key i in
  let s_cipher_bytes = slice (le_quad32_to_bytes s_cipher) 0 (length s) in
  let enc_ctr = aes_encrypt_LE alg key (reverse_bytes_quad32 (inc32 icb_BE i)) in
  let icb_LE = reverse_bytes_quad32 (inc32 icb_BE i) in

  if s = q_bytes_prefix then (
     //  s_cipher_bytes = slice (le_quad32_to_bytes s_cipher) 0 (length s)
     //                 = slice (le_quad32_to_bytes (gctr_encrypt_block icb_BE s_quad alg key i)) 0 (length s)
     //                 = slice (le_quad32_to_bytes (gctr_encrypt_block icb_BE (le_bytes_to_quad32 (pad_to_128_bits s)) alg key i)) 0 (length s)

     // q_cipher_bytes  = gctr_encrypt_block icb_BE q alg key i
    le_quad32_to_bytes_to_quad32 (pad_to_128_bits s);
    slice_pad_to_128_bits s;
    quad32_xor_bytewise q (le_bytes_to_quad32 (pad_to_128_bits s)) (aes_encrypt_LE alg key icb_LE) (length s);
    //assert (equal s_cipher_bytes q_cipher_bytes);
    ()
  ) else
    ();
  ()

#reset-options "--z3rlimit 30"
open FStar.Seq.Properties

let gctr_partial_to_full_advanced (icb_BE:quad32) (plain:seq quad32) (cipher:seq quad32) (alg:algorithm) (key:seq nat32) (num_bytes:nat) =
  reveal_opaque gctr_encrypt_LE_def;
  let num_blocks = num_bytes / 16 in
  let plain_bytes = slice (le_seq_quad32_to_bytes plain) 0 num_bytes in
  let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 num_bytes in
  step1 plain num_bytes;
  let s = slice (le_seq_quad32_to_bytes plain) (num_blocks * 16) num_bytes in
  let final_p = index plain num_blocks in
  step2 s final_p icb_BE alg key num_blocks;

  let num_extra = num_bytes % 16 in
  let full_bytes_len = num_bytes - num_extra in
  let full_blocks, final_block = split plain_bytes full_bytes_len in
  assert (full_bytes_len % 16 == 0);
  assert (length full_blocks == full_bytes_len);
  let full_quads_LE = le_bytes_to_seq_quad32 full_blocks in
  let final_quad_LE = le_bytes_to_quad32 (pad_to_128_bits final_block) in
  let cipher_quads_LE = gctr_encrypt_recursive icb_BE full_quads_LE alg key 0 in
  let final_cipher_quad_LE = gctr_encrypt_block icb_BE final_quad_LE alg key (full_bytes_len / 16) in
  assert (cipher_quads_LE == slice cipher 0 num_blocks);   // LHS quads
  let cipher_bytes_full_LE = le_seq_quad32_to_bytes cipher_quads_LE in
  let final_cipher_bytes_LE = slice (le_quad32_to_bytes final_cipher_quad_LE) 0 num_extra in

  assert (le_seq_quad32_to_bytes cipher_quads_LE == le_seq_quad32_to_bytes (slice cipher 0 num_blocks)); // LHS bytes

  assert (length s == num_extra);
  let q_prefix = slice (le_quad32_to_bytes final_p) 0 num_extra in
  le_seq_quad32_to_bytes_tail_prefix plain num_bytes;
  assert (q_prefix == s);

  assert(final_cipher_bytes_LE == slice (le_quad32_to_bytes (index cipher num_blocks)) 0 num_extra); // RHS bytes

  le_seq_quad32_to_bytes_tail_prefix cipher num_bytes;
  assert (slice (le_quad32_to_bytes (index cipher num_blocks)) 0 num_extra ==
          slice (le_seq_quad32_to_bytes cipher) (num_blocks * 16) num_bytes);

  slice_commutes_le_seq_quad32_to_bytes0 cipher num_blocks;
  assert (le_seq_quad32_to_bytes (slice cipher 0 num_blocks) == slice (le_seq_quad32_to_bytes cipher) 0 (num_blocks * 16));


  assert (slice (slice (le_seq_quad32_to_bytes cipher) (num_blocks * 16) (length cipher * 16)) 0 num_extra ==
          slice (le_seq_quad32_to_bytes cipher) (num_blocks * 16) num_bytes);
  slice_append_adds (le_seq_quad32_to_bytes cipher) (num_blocks * 16) num_bytes;
  assert (slice (le_seq_quad32_to_bytes cipher) 0 (num_blocks * 16) @|
          slice (le_seq_quad32_to_bytes cipher) (num_blocks * 16) num_bytes ==
          slice (le_seq_quad32_to_bytes cipher) 0 num_bytes);
  assert (cipher_bytes == (le_seq_quad32_to_bytes (slice cipher 0 num_blocks)) @| slice (le_quad32_to_bytes (index cipher num_blocks)) 0 num_extra);
  ()


let gctr_encrypt_one_block (icb_BE plain:quad32) (alg:algorithm) (key:seq nat32) =
  reveal_opaque gctr_encrypt_LE_def;
  assert(inc32 icb_BE 0 == icb_BE);
  let encrypted_icb = aes_encrypt_BE alg key icb_BE in
  let p = le_quad32_to_bytes plain in
  let plain_quads_LE = le_bytes_to_seq_quad32 p in
  let p_seq = create 1 plain in
  assert (length p == 16);
  le_bytes_to_seq_quad32_to_bytes_one_quad plain;
  assert (p_seq == plain_quads_LE);
  let cipher_quads_LE = gctr_encrypt_recursive icb_BE plain_quads_LE alg key 0 in
  assert (cipher_quads_LE == cons (gctr_encrypt_block icb_BE (head plain_quads_LE) alg key 0) (gctr_encrypt_recursive icb_BE (tail plain_quads_LE) alg key (1)));
  assert (head plain_quads_LE == plain);

  assert (gctr_encrypt_block icb_BE (head plain_quads_LE) alg key 0 ==
          (let icb_LE = reverse_bytes_quad32 (inc32 icb_BE 0) in
           quad32_xor (head plain_quads_LE) (aes_encrypt_LE alg key icb_LE)));
  assert (quad32_xor plain (aes_encrypt_LE alg key (reverse_bytes_quad32 icb_BE))
          ==
          (let icb_LE = reverse_bytes_quad32 (inc32 icb_BE 0) in
           quad32_xor (head plain_quads_LE) (aes_encrypt_LE alg key icb_LE)));
  assert (gctr_encrypt_block icb_BE (head plain_quads_LE) alg key 0 == quad32_xor plain (aes_encrypt_LE alg key (reverse_bytes_quad32 icb_BE)));
  FStar.Pervasives.reveal_opaque (`%aes_encrypt_le) aes_encrypt_le;
  assert (gctr_encrypt_block icb_BE (head plain_quads_LE) alg key 0 == quad32_xor plain (aes_encrypt_BE alg key icb_BE));
  assert (gctr_encrypt_block icb_BE (head plain_quads_LE) alg key 0 == quad32_xor plain encrypted_icb);
  assert(gctr_encrypt_recursive icb_BE (tail p_seq) alg key 1 == empty);   // OBSERVE
  //assert(gctr_encrypt_LE icb p alg key == cons (quad32_xor plain encrypted_icb) empty);
  let x = quad32_xor plain encrypted_icb in
  append_empty_r (create 1 x);                 // This is the missing piece
  ()



let lemma_length_simplifier (s bytes t:seq quad32) (num_bytes:nat) : Lemma
  (requires t == (if num_bytes > (length s) * 16 then append s bytes else s) /\
            (num_bytes <= (length s) * 16 ==> num_bytes == (length s * 16)) /\
            length s * 16 <= num_bytes /\
            num_bytes < length s * 16 + 16 /\
            length bytes == 1
            )
  (ensures slice (le_seq_quad32_to_bytes t) 0 num_bytes ==
           slice (le_seq_quad32_to_bytes (append s bytes)) 0 num_bytes)
  =
  if num_bytes > (length s) * 16 then (
    ()
  ) else (
    calc (==) {
        slice (le_seq_quad32_to_bytes (append s bytes)) 0 num_bytes;
          == { append_distributes_le_seq_quad32_to_bytes s bytes }
        slice (append (le_seq_quad32_to_bytes s) (le_seq_quad32_to_bytes bytes)) 0 num_bytes;
          == { Vale.Lib.Seqs.lemma_slice_first_exactly_in_append (le_seq_quad32_to_bytes s) (le_seq_quad32_to_bytes bytes) }
        le_seq_quad32_to_bytes s;
          == { assert (length (le_seq_quad32_to_bytes s) == num_bytes) }
        slice (le_seq_quad32_to_bytes s) 0 num_bytes;
    };
    ()
  )

let gctr_bytes_helper (alg:algorithm) (key:seq nat32)
                      (p128 p_bytes c128 c_bytes:seq quad32)
                      (p_num_bytes:nat)
                      (iv_BE:quad32) : Lemma
  (requires length p128 * 16 < pow2_32 /\
           length p128 * 16 <= p_num_bytes /\
           p_num_bytes < length p128 * 16 + 16 /\
           length p128 == length c128 /\
           length p_bytes == 1 /\
           length c_bytes == 1 /\
           is_aes_key_LE alg key /\

          // Ensured by gctr_core_opt
          gctr_partial alg (length p128) p128 c128 key iv_BE /\
          (p_num_bytes > length p128 * 16 ==>
           index c_bytes 0 == gctr_encrypt_block (inc32 iv_BE (length p128)) (index p_bytes 0) alg key 0))
  (ensures (let plain_raw_quads = append p128 p_bytes in
            let plain_bytes = slice (le_seq_quad32_to_bytes plain_raw_quads) 0 p_num_bytes in
            let cipher_raw_quads = append c128 c_bytes in
            let cipher_bytes = slice (le_seq_quad32_to_bytes cipher_raw_quads) 0 p_num_bytes in
            is_gctr_plain_LE plain_bytes /\
            cipher_bytes == gctr_encrypt_LE iv_BE plain_bytes alg key))
  =
  let icb_BE_inc = inc32 iv_BE (length p128) in
  assert (gctr_encrypt_block icb_BE_inc (index p_bytes 0) alg key 0 ==
          gctr_encrypt_block iv_BE (index p_bytes 0) alg key  (length p128));
  FStar.Pervasives.reveal_opaque (`%aes_encrypt_le) aes_encrypt_le;
  //assert (gctr_partial alg 1 p_bytes c_bytes key icb_BE_inc);
  reveal_opaque gctr_partial;

  if p_num_bytes = length p128 * 16 then (
    gctr_partial_completed alg p128 c128 key iv_BE;
    gctr_partial_to_full_basic iv_BE p128 alg key c128;
    assert (le_seq_quad32_to_bytes c128 == gctr_encrypt_LE iv_BE (le_seq_quad32_to_bytes p128) alg key);
    assert (equal (slice (le_seq_quad32_to_bytes p128) 0 p_num_bytes) (le_seq_quad32_to_bytes p128));
    assert (equal (slice (le_seq_quad32_to_bytes c128) 0 p_num_bytes) (le_seq_quad32_to_bytes c128));
    ()
  ) else (
    lemma_gctr_partial_append alg (length p128) 1 p128 c128 p_bytes c_bytes key iv_BE icb_BE_inc;
    let plain = append p128 p_bytes in
    let cipher = append c128 c_bytes in
    let num_blocks = p_num_bytes / 16 in
    //gctr_partial_completed alg plain cipher key iv_BE;
    gctr_partial_completed alg p128 c128 key iv_BE;
    assert (equal (slice plain  0 num_blocks) p128);
    assert (equal (slice cipher 0 num_blocks) c128);
    gctr_partial_to_full_advanced iv_BE (append p128 p_bytes) (append c128 c_bytes) alg key p_num_bytes
  );
  lemma_length_simplifier p128 p_bytes (if p_num_bytes > length p128 * 16 then append p128 p_bytes else p128) p_num_bytes;
  lemma_length_simplifier c128 c_bytes (if p_num_bytes > length c128 * 16 then append c128 c_bytes else c128) p_num_bytes;
  ()

