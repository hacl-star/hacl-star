module Vale.AES.GCTR

open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open FStar.Seq
open Vale.AES.AES_s
open Vale.AES.GCTR_s
open Vale.AES.GCM_helpers
open FStar.Math.Lemmas
open Vale.Lib.Seqs

let make_gctr_plain_LE (p:seq nat8) : seq nat8 =
  if length p < pow2_32 then p else empty

let inc32lite (cb:quad32) (i:int) : quad32 =
  if 0 <= i && i < pow2_32 then
    let sum = cb.lo0 + i in
    let lo0 = if sum >= pow2_32 then sum - pow2_32 else sum in
    Mkfour lo0 cb.lo1 cb.hi2 cb.hi3
  else
    Mkfour 42 42 42 42

let empty_seq_quad32 : seq quad32 = empty

let lemma_counter_init (x:quad32) (low64 low8:nat64) : Lemma
  (requires low64 == lo64 x /\
            low8  == iand64 low64 0xff)
  (ensures  low8 == x.lo0 % 256)
  =
  Vale.Poly1305.Bitvectors.lemma_bytes_and_mod1 low64;
  Vale.Def.TypesNative_s.reveal_iand 64 low64 0xff;
  assert (low8 == low64 % 256);
  Vale.Def.Opaque_s.reveal_opaque lo64_def;
  assert_norm (pow2_norm 32 == pow2_32);      // OBSERVE
  assert (low64 == x.lo0 + x.lo1 * pow2_32);  // OBSERVE
  assert (low64 % 256 == x.lo0 % 256);
  ()

let partial_seq_agreement (x y:seq quad32) (lo hi:nat) =
  lo <= hi /\ hi <= length x /\ hi <= length y /\
  (forall i . {:pattern (index x i) \/ (index y i)} lo <= i /\ i < hi ==> index x i == index y i)

(*
let lemma_partial_seq_agreement_subset (x y:seq quad32) (lo hi hi':nat) : Lemma
  (requires lo <= hi /\ hi <= hi' /\ hi' <= length x /\ hi' <= length y /\
            partial_seq_agreement x y lo hi')
  (ensures partial_seq_agreement x y lo hi)
  =
  ()
*)
(*
let lemma_partial_seq_agreement_step (x y z:seq quad32) (lo mid hi:nat) : Lemma
  (requires partial_seq_agreement x y lo hi /\
            length z >= hi /\
            lo <= mid /\ mid < hi /\
            (forall i . 0 <= i /\ i < length z /\ (i < lo || i > mid) ==>
                   index y i == index z i))
  (ensures partial_seq_agreement x z (mid+1) hi)
  =
  ()
*)

val gctr_encrypt_block_offset (icb_BE:quad32) (plain_LE:quad32) (alg:algorithm) (key:seq nat32) (i:int) : Lemma
  (requires is_aes_key_LE alg key)
  (ensures
    gctr_encrypt_block icb_BE plain_LE alg key i ==
      gctr_encrypt_block (inc32 icb_BE i) plain_LE alg key 0
  )

val gctr_encrypt_empty (icb_BE:quad32) (plain_LE cipher_LE:seq quad32) (alg:algorithm) (key:seq nat32) : Lemma
  (requires is_aes_key_LE alg key)
  (ensures (
    let plain = slice (le_seq_quad32_to_bytes plain_LE) 0 0 in
    let cipher = slice (le_seq_quad32_to_bytes cipher_LE) 0 0 in
    cipher = gctr_encrypt_LE icb_BE (make_gctr_plain_LE plain) alg key
  ))

[@"opaque_to_smt"]
let aes_encrypt_le = aes_encrypt_LE_def

let aes_encrypt_BE (alg:algorithm) (key:seq nat32) (p_BE:quad32) : Pure quad32
  (requires is_aes_key_LE alg key)
  (ensures fun _ -> True)
  =
  let p_LE = reverse_bytes_quad32 p_BE in
  aes_encrypt_le alg key p_LE

let gctr_registers_def (r0 r1 r2 r3 r4 r5:quad32) (s:seq quad32) (alg:algorithm) (key:seq nat32) (ctr_BE:quad32) (i:int) : prop0 =
  0 <= i /\ i*6 + 5 < length s /\
  is_aes_key_LE alg key /\
  r0 = quad32_xor (index s (i*6 + 0)) (aes_encrypt_BE alg key (inc32lite ctr_BE (6*i + 0))) /\
  r1 = quad32_xor (index s (i*6 + 1)) (aes_encrypt_BE alg key (inc32lite ctr_BE (6*i + 1))) /\
  r2 = quad32_xor (index s (i*6 + 2)) (aes_encrypt_BE alg key (inc32lite ctr_BE (6*i + 2))) /\
  r3 = quad32_xor (index s (i*6 + 3)) (aes_encrypt_BE alg key (inc32lite ctr_BE (6*i + 3))) /\
  r4 = quad32_xor (index s (i*6 + 4)) (aes_encrypt_BE alg key (inc32lite ctr_BE (6*i + 4))) /\
  r5 = quad32_xor (index s (i*6 + 5)) (aes_encrypt_BE alg key (inc32lite ctr_BE (6*i + 5)))

let gctr_registers = make_opaque gctr_registers_def

let gctr_partial (alg:algorithm) (bound:nat) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : prop0 =
  is_aes_key_LE alg key /\
  ( let bound = min bound (min (length plain) (length cipher)) in
    forall j . {:pattern (index cipher j)} 0 <= j /\ j < bound ==>
      index cipher j == quad32_xor (index plain j) (aes_encrypt_BE alg key (inc32 icb j)))

let gctr_partial_opaque = make_opaque gctr_partial

let gctr_partial_opaque_init (alg:algorithm) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires is_aes_key_LE alg key)
  (ensures gctr_partial_opaque alg 0 plain cipher key icb)
  =
  reveal_opaque gctr_partial;
  ()

let lemma_gctr_partial_append (alg:algorithm) (b1 b2:nat) (p1 c1 p2 c2:seq quad32) (key:seq nat32) (icb1 icb2:quad32) : Lemma
  (requires gctr_partial_opaque alg b1 p1 c1 key icb1 /\
            gctr_partial_opaque alg b2 p2 c2 key icb2 /\
            b1 == length p1 /\ b1 == length c1 /\
            b2 == length p2 /\ b2 == length c2 /\
            icb2 == inc32 icb1 b1)
  (ensures gctr_partial_opaque alg (b1 + b2) (p1 @| p2) (c1 @| c2) key icb1)
  =
  reveal_opaque gctr_partial;
  ()

let gctr_partial_opaque_ignores_postfix (alg:algorithm) (bound:nat32) (plain plain' cipher cipher':seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires is_aes_key_LE alg key /\
            length plain >= bound /\
            length cipher >= bound /\
            length plain' >= bound /\
            length cipher' >= bound /\
            slice plain  0 bound == slice plain'  0 bound /\
            slice cipher 0 bound == slice cipher' 0 bound)
  (ensures gctr_partial_opaque alg bound plain cipher key icb <==> gctr_partial_opaque alg bound plain' cipher' key icb)
  =
  reveal_opaque gctr_partial;
  // OBSERVE:
  assert (forall i . 0 <= i /\ i < bound ==> index plain i == index (slice plain 0 bound) i);
  assert (forall i . 0 <= i /\ i < bound ==> index plain' i == index (slice plain' 0 bound) i);
  assert (forall i . 0 <= i /\ i < bound ==> index cipher i == index (slice cipher 0 bound) i);
  assert (forall i . 0 <= i /\ i < bound ==> index cipher' i == index (slice cipher' 0 bound) i);
  ()

val gctr_partial_extend6 (alg:algorithm) (bound:nat) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires length plain >= bound + 6 /\
            length cipher >= bound + 6 /\
            is_aes_key_LE alg key /\
            bound + 6 < pow2_32 /\
            gctr_partial_opaque alg bound plain cipher key icb /\
            index cipher (bound + 0) == quad32_xor (index plain (bound + 0)) (aes_encrypt_BE alg key (inc32lite icb (bound + 0))) /\
            index cipher (bound + 1) == quad32_xor (index plain (bound + 1)) (aes_encrypt_BE alg key (inc32lite icb (bound + 1))) /\
            index cipher (bound + 2) == quad32_xor (index plain (bound + 2)) (aes_encrypt_BE alg key (inc32lite icb (bound + 2))) /\
            index cipher (bound + 3) == quad32_xor (index plain (bound + 3)) (aes_encrypt_BE alg key (inc32lite icb (bound + 3))) /\
            index cipher (bound + 4) == quad32_xor (index plain (bound + 4)) (aes_encrypt_BE alg key (inc32lite icb (bound + 4))) /\
            index cipher (bound + 5) == quad32_xor (index plain (bound + 5)) (aes_encrypt_BE alg key (inc32lite icb (bound + 5)))
  )
  (ensures gctr_partial_opaque alg (bound + 6) plain cipher key icb)

val gctr_partial_completed (alg:algorithm) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires
    is_aes_key_LE alg key /\
    length plain == length cipher /\
    length plain < pow2_32 /\
    gctr_partial alg (length cipher) plain cipher key icb
  )
  (ensures cipher == gctr_encrypt_recursive icb plain alg key 0)

val gctr_partial_opaque_completed (alg:algorithm) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires
    is_aes_key_LE alg key /\
    length plain == length cipher /\
    length plain < pow2_32 /\
    gctr_partial_opaque alg (length cipher) plain cipher key icb
  )
  (ensures cipher == gctr_encrypt_recursive icb plain alg key 0)

val gctr_partial_to_full_basic (icb_BE:quad32) (plain:seq quad32) (alg:algorithm) (key:seq nat32) (cipher:seq quad32) : Lemma
  (requires
    is_aes_key_LE alg key /\
    cipher == gctr_encrypt_recursive icb_BE plain alg key 0 /\
    length plain * 16 < pow2_32
  )
  (ensures le_seq_quad32_to_bytes cipher == gctr_encrypt_LE icb_BE (le_seq_quad32_to_bytes plain) alg key)

open FStar.Seq.Properties

val gctr_partial_to_full_advanced (icb_BE:quad32) (plain:seq quad32) (cipher:seq quad32) (alg:algorithm) (key:seq nat32) (num_bytes:nat) : Lemma
  (requires
    is_aes_key_LE alg key /\
    1 <= num_bytes /\
    num_bytes < 16 * length plain /\
    16 * (length plain - 1) < num_bytes /\
    num_bytes % 16 <> 0 /\ num_bytes < pow2_32 /\
    length plain == length cipher /\
    ( let num_blocks = num_bytes / 16 in
      slice cipher 0 num_blocks == gctr_encrypt_recursive icb_BE (slice plain 0 num_blocks) alg key 0 /\
      index cipher num_blocks == gctr_encrypt_block icb_BE (index plain num_blocks) alg key num_blocks)
  )
  (ensures (
    let plain_bytes = slice (le_seq_quad32_to_bytes plain) 0 num_bytes in
    let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 num_bytes in
    cipher_bytes == gctr_encrypt_LE icb_BE plain_bytes alg key
  ))

val gctr_encrypt_one_block (icb_BE plain:quad32) (alg:algorithm) (key:seq nat32) : Lemma
  (requires is_aes_key_LE alg key)
  (ensures
    gctr_encrypt_LE icb_BE (le_quad32_to_bytes plain) alg key ==
      le_seq_quad32_to_bytes (create 1 (quad32_xor plain (aes_encrypt_BE alg key icb_BE)))
  )

val gctr_bytes_helper (alg:algorithm) (key:seq nat32)
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

