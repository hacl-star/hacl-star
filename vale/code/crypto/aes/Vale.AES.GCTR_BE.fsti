module Vale.AES.GCTR_BE

open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open FStar.Seq
open Vale.AES.AES_BE_s
open Vale.AES.GCTR_BE_s
open FStar.Math.Lemmas
open Vale.Def.Words.Seq_s

let make_gctr_plain_BE (p:seq nat8) : seq nat8 =
  if length p < pow2_32 then p else empty

let inc32lite (cb:quad32) (i:int) : quad32 =
  if 0 <= i && i < pow2_32 then
    let sum = cb.lo0 + i in
    let lo0 = if sum >= pow2_32 then sum - pow2_32 else sum in
    Mkfour lo0 cb.lo1 cb.hi2 cb.hi3
  else
    Mkfour 42 42 42 42

let empty_seq_quad32 : seq quad32 = empty

let partial_seq_agreement (x y:seq quad32) (lo hi:nat) =
  lo <= hi /\ hi <= length x /\ hi <= length y /\
  (forall i . {:pattern (index x i) \/ (index y i)} lo <= i /\ i < hi ==> index x i == index y i)

let lemma_eq_reverse_bytes_quad32_seq (s1 s2 s3:seq quad32) (bound:nat) (icb:quad32) (alg:algorithm) (key:seq nat32) :
  Lemma 
  (requires (is_aes_key_word alg key /\ bound <= length s1 /\ bound <= length s2 /\ bound <= length s3 /\
      (forall j . {:pattern (index s2 j)} 0 <= j /\ j < bound ==>
      index s2 j == quad32_xor (index s3 j) (aes_encrypt_word alg key (inc32 icb j))) /\ 
      (forall j . {:pattern (index s1 j)} 0 <= j /\ j < bound ==>
      index s1 j == index s2 j)))
  (ensures
    (forall j . {:pattern (index s1 j)} 0 <= j /\ j < bound ==>
      index s1 j == quad32_xor (index s3 j) (aes_encrypt_word alg key (inc32 icb j)))
  )
  =
  ()

val gctr_encrypt_block_offset (icb:quad32) (plain:quad32) (alg:algorithm) (key:seq nat32) (i:int) : Lemma
  (requires is_aes_key_word alg key)
  (ensures
    gctr_encrypt_block icb plain alg key i ==
      gctr_encrypt_block (inc32 icb i) plain alg key 0
  )

let gctr_partial_def (alg:algorithm) (bound:nat) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : prop0 =
  is_aes_key_word alg key /\
  ( let bound = min bound (min (length plain) (length cipher)) in
    forall j . {:pattern (index cipher j)} 0 <= j /\ j < bound ==>
      index cipher j == quad32_xor (index plain j) (aes_encrypt_word alg key (inc32 icb j)))
[@"opaque_to_smt"] let gctr_partial = opaque_make gctr_partial_def
irreducible let gctr_partial_reveal = opaque_revealer (`%gctr_partial) gctr_partial gctr_partial_def

val gctr_partial_opaque_init (alg:algorithm) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires is_aes_key_word alg key)
  (ensures gctr_partial alg 0 plain cipher key icb)

val lemma_gctr_partial_append (alg:algorithm) (b1 b2:nat) (p1 c1 p2 c2:seq quad32) (key:seq nat32) (icb1 icb2:quad32) : Lemma
  (requires gctr_partial alg b1 p1 c1 key icb1 /\
            gctr_partial alg b2 p2 c2 key icb2 /\
            b1 == length p1 /\ b1 == length c1 /\
            b2 == length p2 /\ b2 == length c2 /\
            icb2 == inc32 icb1 b1)
  (ensures gctr_partial alg (b1 + b2) (p1 @| p2) (c1 @| c2) key icb1)

val gctr_partial_opaque_ignores_postfix (alg:algorithm) (bound:nat32) (plain plain' cipher cipher':seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires is_aes_key_word alg key /\
            length plain >= bound /\
            length cipher >= bound /\
            length plain' >= bound /\
            length cipher' >= bound /\
            slice plain  0 bound == slice plain'  0 bound /\
            slice cipher 0 bound == slice cipher' 0 bound)
  (ensures gctr_partial alg bound plain cipher key icb <==> gctr_partial alg bound plain' cipher' key icb)

val gctr_partial_completed (alg:algorithm) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires
    is_aes_key_word alg key /\
    length plain == length cipher /\
    length plain < pow2_32 /\
    gctr_partial_def alg (length cipher) plain cipher key icb
  )
  (ensures cipher == gctr_encrypt_recursive icb plain alg key 0)

val gctr_partial_opaque_completed (alg:algorithm) (plain cipher:seq quad32) (key:seq nat32) (icb:quad32) : Lemma
  (requires
    is_aes_key_word alg key /\
    length plain == length cipher /\
    length plain < pow2_32 /\
    gctr_partial alg (length cipher) plain cipher key icb
  )
  (ensures cipher == gctr_encrypt_recursive icb plain alg key 0)

val gctr_partial_to_full_basic (icb:quad32) (plain:seq quad32) (alg:algorithm) (key:seq nat32) (cipher:seq quad32) : Lemma
  (requires
    is_aes_key_word alg key /\
    cipher == gctr_encrypt_recursive icb plain alg key 0 /\
    length plain * 16 < pow2_32
  )
  (ensures seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher) == gctr_encrypt icb (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) alg key)

open FStar.Seq.Properties

val gctr_partial_to_full_advanced (icb_BE:quad32) (plain:seq quad32) (cipher:seq quad32) (alg:algorithm) (key:seq nat32) (num_bytes:nat) : Lemma
  (requires
    is_aes_key_word alg key /\
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
    let plain_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE plain)) 0 num_bytes in
    let cipher_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher)) 0 num_bytes in
    cipher_bytes == gctr_encrypt icb_BE plain_bytes alg key
  ))

val gctr_encrypt_one_block (icb plain:quad32) (alg:algorithm) (key:seq nat32) : Lemma
  (requires is_aes_key_word alg key)
  (ensures
    gctr_encrypt icb (be_quad32_to_bytes plain) alg key ==
      seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (create 1 (quad32_xor plain (aes_encrypt_word alg key icb))))
  )
