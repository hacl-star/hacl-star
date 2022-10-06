module Vale.SHA.PPC64LE.SHA_helpers

open FStar.Mul
open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.Def.Types_s
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open FStar.Seq
open Vale.Arch.Types
open Vale.Def.Sel
open Vale.SHA2.Wrapper
open Vale.Def.Words.Four_s

unfold let (.[]) = FStar.Seq.index

#reset-options "--max_fuel 0 --max_ifuel 0"

// Specialize these definitions (from Spec.SHA2.fst) for SHA256
unfold let size_k_w_256 = 64
val word:Type0
(* Number of words for a block size *)
let size_block_w_256 = 16
(* Define the size block in bytes *)
let block_length =
  4 (*word_length a*) * size_block_w_256
let block_w  = m:seq word {length m = size_block_w_256}
let counter = nat
val k : (s:seq word {length s = size_k_w_256})
let hash256 = m:Seq.seq word {Seq.length m = 8}

(* Input data. *)
type byte = UInt8.t
type bytes = Seq.seq byte

(* Input data, multiple of a block length. *)
let bytes_blocks =
  l:bytes { Seq.length l % block_length = 0 }

// Hide various SHA2 definitions
val ws_opaque (b:block_w) (t:counter{t < size_k_w_256}):nat32
val shuffle_core_opaque (block:block_w) (hash:hash256) (t:counter{t < size_k_w_256}):hash256
val update_multi_opaque (hash:hash256) (blocks:bytes_blocks):hash256
val update_multi_transparent (hash:hash256) (blocks:bytes_blocks):hash256

// Hide some functions that operate on words & bytes
val word_to_nat32 (x:word) : nat32
val nat32_to_word (x:nat32) : word

//unfold let bytes_blocks256 = bytes_blocks SHA2_256
let repeat_range_vale (max:nat { max < size_k_w_256}) (block:block_w) (hash:hash256) =
  Spec.Loops.repeat_range 0 max (shuffle_core_opaque block) hash
let update_multi_opaque_vale (hash:hash256) (blocks:bytes) : hash256 =
  if length blocks % size_k_w_256 = 0 then let b:bytes_blocks = blocks in update_multi_opaque hash b else hash

val make_ordered_hash (abcd efgh:quad32): Pure (hash256)
  (requires True)
  (ensures fun hash ->
         length hash == 8 /\
         hash.[0] == nat32_to_word abcd.lo0 /\
         hash.[1] == nat32_to_word abcd.lo1 /\
         hash.[2] == nat32_to_word abcd.hi2 /\
         hash.[3] == nat32_to_word abcd.hi3 /\
         hash.[4] == nat32_to_word efgh.lo0 /\
         hash.[5] == nat32_to_word efgh.lo1 /\
         hash.[6] == nat32_to_word efgh.hi2 /\
         hash.[7] == nat32_to_word efgh.hi3
  )

val update_block (hash:hash256) (block:block_w): hash256

val lemma_update_multi_opaque_vale_is_update_multi (hash:hash256) (blocks:bytes) : Lemma
  (requires length blocks % 64 = 0)
  (ensures  update_multi_opaque_vale hash blocks == update_multi_transparent hash blocks)

val sigma_0_0_partial_def (t:counter) (block:block_w) : nat32
[@"opaque_to_smt"] let sigma_0_0_partial = opaque_make sigma_0_0_partial_def
irreducible let sigma_0_0_partial_reveal = opaque_revealer (`%sigma_0_0_partial) sigma_0_0_partial sigma_0_0_partial_def

val lemma_sha256_sigma0 (src:quad32) (t:counter) (block:block_w) : Lemma
  (requires 16 <= t /\ t < size_k_w_256 /\
            src.hi3 == ws_opaque block (t-15))
  (ensures (sigma256_0_0 src.hi3 == sigma_0_0_partial t block))

val sigma_0_1_partial_def (t:counter) (block:block_w) : nat32
[@"opaque_to_smt"] let sigma_0_1_partial = opaque_make sigma_0_1_partial_def
irreducible let sigma_0_1_partial_reveal = opaque_revealer (`%sigma_0_1_partial) sigma_0_1_partial sigma_0_1_partial_def

val lemma_sha256_sigma1 (src:quad32) (t:counter) (block:block_w) : Lemma
  (requires 16 <= t /\ t < size_k_w_256 /\
            src.hi3 == ws_opaque block (t-2))
  (ensures (sigma256_0_1 src.hi3 == sigma_0_1_partial t block))

val sigma_1_0_partial_def (t:counter) (block:block_w) (hash_orig:hash256) : nat32
[@"opaque_to_smt"] let sigma_1_0_partial = opaque_make sigma_1_0_partial_def
irreducible let sigma_1_0_partial_reveal = opaque_revealer (`%sigma_1_0_partial) sigma_1_0_partial sigma_1_0_partial_def

val lemma_sha256_sigma2 (src:quad32) (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w_256 /\
            src.hi3 == word_to_nat32 ((repeat_range_vale t block hash_orig).[0]))
  (ensures (sigma256_1_0 src.hi3 == sigma_1_0_partial t block hash_orig))

val sigma_1_1_partial_def (t:counter) (block:block_w) (hash_orig:hash256) : nat32
[@"opaque_to_smt"] let sigma_1_1_partial = opaque_make sigma_1_1_partial_def
irreducible let sigma_1_1_partial_reveal = opaque_revealer (`%sigma_1_1_partial) sigma_1_1_partial sigma_1_1_partial_def

val lemma_sha256_sigma3 (src:quad32) (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w_256 /\
            src.hi3 == word_to_nat32 ((repeat_range_vale t block hash_orig).[4]))
  (ensures (sigma256_1_1 src.hi3 == sigma_1_1_partial t block hash_orig))

val make_seperated_hash (a b c d e f g h:nat32): Pure (hash256)
  (requires True)
  (ensures fun hash ->
         length hash == 8 /\
         hash.[0] == nat32_to_word a /\
         hash.[1] == nat32_to_word b /\
         hash.[2] == nat32_to_word c /\
         hash.[3] == nat32_to_word d /\
         hash.[4] == nat32_to_word e /\
         hash.[5] == nat32_to_word f /\
         hash.[6] == nat32_to_word g /\
         hash.[7] == nat32_to_word h
  )

val make_seperated_hash_quad32 (a b c d e f g h:quad32): Pure (hash256)
  (requires True)
  (ensures fun hash ->
         length hash == 8 /\
         hash.[0] == nat32_to_word a.hi3 /\
         hash.[1] == nat32_to_word b.hi3 /\
         hash.[2] == nat32_to_word c.hi3 /\
         hash.[3] == nat32_to_word d.hi3 /\
         hash.[4] == nat32_to_word e.hi3 /\
         hash.[5] == nat32_to_word f.hi3 /\
         hash.[6] == nat32_to_word g.hi3 /\
         hash.[7] == nat32_to_word h.hi3
  )

val lemma_make_seperated_hash (hash:hash256) (a b c d e f g h:quad32) : Lemma
  (requires length hash == 8 /\
            a.hi3 == word_to_nat32 hash.[0] /\
            b.hi3 == word_to_nat32 hash.[1] /\
            c.hi3 == word_to_nat32 hash.[2] /\
            d.hi3 == word_to_nat32 hash.[3] /\
            e.hi3 == word_to_nat32 hash.[4] /\
            f.hi3 == word_to_nat32 hash.[5] /\
            g.hi3 == word_to_nat32 hash.[6] /\
            h.hi3 == word_to_nat32 hash.[7])
  (ensures hash == make_seperated_hash_quad32 a b c d e f g h)

val lemma_vsel32 (a b c:nat32) : Lemma
  (ensures (isel32 a b c = (iand32 c a) *^ (iand32 (inot32 c) b)))

val ch_256 (x y z:nat32):Pure(nat32)
  (requires True)
  (ensures fun a -> a == (iand32 x y) *^ (iand32 (inot32 x) z))

val lemma_eq_maj_xvsel32 (a b c:nat32) : Lemma
  (ensures (isel32 c b (a *^ b) = (iand32 a b) *^ ((iand32 a c) *^ (iand32 b c))))

val maj_256 (x y z:nat32):Pure(nat32)
  (requires True)
  (ensures fun a -> a == (iand32 x y) *^ ((iand32 x z) *^ (iand32 y z)))

val lemma_sigma_0_0_partial (t:counter) (block:block_w) : Lemma
  (requires 16 <= t /\ t < size_k_w_256)
  (ensures (sigma256_0_0 (ws_opaque block (t-15)) == sigma_0_0_partial t block))

val lemma_sigma_0_1_partial (t:counter) (block:block_w) : Lemma
  (requires 16 <= t /\ t < size_k_w_256)
  (ensures (sigma256_0_1 (ws_opaque block (t-2)) == sigma_0_1_partial t block))

val lemma_sigma_1_0_partial (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w_256)
  (ensures (sigma256_1_0 (word_to_nat32 ((repeat_range_vale t block hash_orig).[0])) == sigma_1_0_partial t block hash_orig))

val lemma_sigma_1_1_partial (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w_256)
  (ensures (sigma256_1_1 (word_to_nat32 ((repeat_range_vale t block hash_orig).[4])) == sigma_1_1_partial t block hash_orig))

(* Abbreviations and lemmas for the code itself *)
let k_reqs (k_seq:seq quad32) : prop0 =
  length k_seq == size_k_w_256 / 4 /\
  (forall i . {:pattern (index k_seq i)} 0 <= i /\ i < (size_k_w_256/4) ==>
    (k_seq.[i]).lo0 == word_to_nat32 (k.[4 * i]) /\
    (k_seq.[i]).lo1 == word_to_nat32 (k.[4 * i + 1]) /\
    (k_seq.[i]).hi2 == word_to_nat32 (k.[4 * i + 2]) /\
    (k_seq.[i]).hi3 == word_to_nat32 (k.[4 * i + 3]))

let quads_to_block_be (qs:seq quad32) : block_w
  =
  let nat32_seq = Vale.Def.Words.Seq_s.seq_four_to_seq_BE qs in
  let f (n:nat{n < 16}) : word = nat32_to_word (if n < length nat32_seq then nat32_seq.[n] else 0) in
  init 16 f

val lemma_quads_to_block_be (qs:seq quad32) : Lemma
  (requires length qs == 4)
  (ensures
  (let block = quads_to_block_be qs in
            forall i . {:pattern (index qs i)} 0 <= i /\ i < 4 ==>
              (qs.[i]).hi3 == ws_opaque block (4 * i + 0) /\
              (qs.[i]).hi2 == ws_opaque block (4 * i + 1) /\
              (qs.[i]).lo1 == ws_opaque block (4 * i + 2) /\
              (qs.[i]).lo0 == ws_opaque block (4 * i + 3)))

let k_index (ks:seq quad32) (i:nat) : nat32 =
  if length ks = size_k_w_256 / 4 && i < size_k_w_256 then four_select ks.[(i/4)] (i % 4)
  else 0


val lemma_shuffle_core_properties (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w_256)
  (ensures (let hash = Spec.Loops.repeat_range 0 t (shuffle_core_opaque block) hash_orig in
            let h = Spec.Loops.repeat_range 0 (t + 1) (shuffle_core_opaque block) hash_orig in
            let a0 = word_to_nat32 hash.[0] in
            let b0 = word_to_nat32 hash.[1] in
            let c0 = word_to_nat32 hash.[2] in
            let d0 = word_to_nat32 hash.[3] in
            let e0 = word_to_nat32 hash.[4] in
            let f0 = word_to_nat32 hash.[5] in
            let g0 = word_to_nat32 hash.[6] in
            let h0 = word_to_nat32 hash.[7] in
            let t1 = add_wrap (add_wrap (add_wrap (add_wrap h0 (sigma256_1_1 e0)) (ch_256 e0 f0 g0)) (word_to_nat32 k.[t])) (ws_opaque block t) in
            let t2 = add_wrap (sigma256_1_0 a0) (maj_256 a0 b0 c0) in
            word_to_nat32 h.[0] == add_wrap t1 t2 /\
            word_to_nat32 h.[1] == a0 /\
            word_to_nat32 h.[2] == b0 /\
            word_to_nat32 h.[3] == c0 /\
            word_to_nat32 h.[4] == add_wrap d0 t1 /\
            word_to_nat32 h.[5] == e0 /\
            word_to_nat32 h.[6] == f0 /\
            word_to_nat32 h.[7] == g0))

val lemma_ws_opaque (block:block_w) (t:counter) : Lemma
  (requires 16 <= t && t < size_k_w_256)
  (ensures (let sigma0 = sigma256_0_0 (ws_opaque block (t - 15)) in
            let sigma1 = sigma256_0_1 (ws_opaque block (t - 2)) in
            ws_opaque block t == add_wrap (add_wrap (add_wrap sigma1 (ws_opaque block (t - 7))) sigma0) (ws_opaque block (t - 16))))

let repeat_range_vale_64 (block:block_w) (hash:hash256) =
  Spec.Loops.repeat_range 0 64 (shuffle_core_opaque block) hash

val update_lemma (a b c d e f g h a_old b_old c_old d_old e_old f_old g_old h_old a' b' c' d' e' f' g' h':quad32) (block:block_w) : Lemma
  (requires (let hash_orig = make_seperated_hash_quad32 a_old b_old c_old d_old e_old f_old g_old h_old in
             make_seperated_hash_quad32 a b c d e f g h ==
             repeat_range_vale_64 block hash_orig /\
             a' == add_wrap_quad32 a a_old /\
             b' == add_wrap_quad32 b b_old /\
             c' == add_wrap_quad32 c c_old /\
             d' == add_wrap_quad32 d d_old /\
             e' == add_wrap_quad32 e e_old /\
             f' == add_wrap_quad32 f f_old /\
             g' == add_wrap_quad32 g g_old /\
             h' == add_wrap_quad32 h h_old))
  (ensures (let hash_orig = make_seperated_hash_quad32 a_old b_old c_old d_old e_old f_old g_old h_old in
            make_seperated_hash_quad32 a' b' c' d' e' f' g' h' == update_block hash_orig block))

let rec update_multi_quads (s:seq quad32) (hash_orig:hash256) : Tot (hash256) (decreases (length s))
  =
  if length s < 4 then
    hash_orig
  else
    let prefix, qs = split s (length s - 4) in
    let h_prefix = update_multi_quads prefix hash_orig in
    let hash = update_block h_prefix (quads_to_block_be qs) in
    hash

val lemma_update_multi_quads (s:seq quad32) (hash_orig:hash256) (bound:nat) : Lemma
    (requires bound + 4 <= length s)
    (ensures (let prefix_LE = slice s 0 bound in
              let prefix_BE = reverse_bytes_quad32_seq prefix_LE in
              let h_prefix = update_multi_quads prefix_BE hash_orig in
              let block_quads_LE = slice s bound (bound + 4) in
              let block_quads_BE = reverse_bytes_quad32_seq block_quads_LE in
              let input_LE = slice s 0 (bound+4) in
              let input_BE = reverse_bytes_quad32_seq input_LE in
              let h = update_block h_prefix (quads_to_block_be block_quads_BE) in
              h == update_multi_quads input_BE hash_orig))

let le_bytes_to_hash (b:seq nat8) : hash256 =
  if length b <> 32 then
     (let f (n:nat{n < 8}) : word = nat32_to_word 0 in
     init 8 f)
  else (
     let open Vale.Def.Words.Seq_s in
     Vale.Lib.Seqs_s.seq_map nat32_to_word (seq_nat8_to_seq_nat32_LE b)
  )

val lemma_hash_to_bytes (s:seq quad32) : Lemma
  (requires length s == 2)
  (ensures make_ordered_hash s.[0] s.[1] == le_bytes_to_hash (le_seq_quad32_to_bytes s))

val lemma_update_multi_equiv_vale (hash hash':hash256) (quads:seq quad32) (r_quads:seq quad32)
  (nat8s:seq nat8) (blocks:seq byte) :
  Lemma (requires length quads % 4 == 0 /\
                  r_quads == reverse_bytes_quad32_seq quads /\
                  nat8s == le_seq_quad32_to_bytes quads /\
                  blocks == seq_nat8_to_seq_uint8 nat8s /\
                  hash' == update_multi_quads r_quads hash)
        (ensures
           length blocks % size_k_w_256 == 0 /\
           hash' == update_multi_opaque_vale hash blocks)
