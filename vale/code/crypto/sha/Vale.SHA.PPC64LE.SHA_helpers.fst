module Vale.SHA.PPC64LE.SHA_helpers

open FStar.Mul
open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Spec.SHA2
open Spec.SHA2.Lemmas
open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Lemmas
open Vale.Def.Types_s
open Vale.Def.Words_s
open FStar.Seq
open FStar.UInt32  // Interop with UInt-based SHA spec
open Vale.Arch.Types
open Vale.Arch.TypesNative
open Vale.Def.Sel
open Vale.SHA2.Wrapper

friend Spec.SHA2
friend Spec.SHA2.Lemmas
friend Vale.SHA2.Wrapper

#reset-options "--max_fuel 0 --max_ifuel 0"

// Define these specific converters here, so that F* only reasons about
// the correctness of the conversion once, rather that at every call site
let vv (u:Lib.IntTypes.uint32) : nat32 = Lib.IntTypes.v u
let to_uint32 (n:nat32) : Lib.IntTypes.uint32 = Lib.IntTypes.u32 n
let word = Lib.IntTypes.uint32
let k = (Spec.SHA2.k0 SHA2_256)

val add_mod_lemma:x:Lib.IntTypes.uint32 -> y:Lib.IntTypes.uint32 ->
		  Lemma (add_mod x y == Lib.IntTypes.(x +. y))
			[SMTPat (Lib.IntTypes.(x +. y))]
let add_mod_lemma x y = ()

unfold let ws_opaque_aux = ws
let ws_opaque (b:block_w) (t:counter{t < size_k_w_256}) : nat32 =
  vv (ws_opaque_aux SHA2_256 b t)

unfold let shuffle_core_opaque_aux = shuffle_core
let shuffle_core_opaque (block:block_w) (hash:hash256) (t:counter{t < size_k_w_256}):hash256 =
  shuffle_core_opaque_aux SHA2_256 block hash t

[@"opaque_to_smt"] let update_multi_opaque_aux = opaque_make update_multi
irreducible let update_multi_reveal = opaque_revealer (`%update_multi_opaque_aux) update_multi_opaque_aux update_multi
let update_multi_opaque (hash:hash256) (blocks:bytes_blocks):hash256 =
  update_multi_opaque_aux SHA2_256 hash () blocks

let update_multi_transparent (hash:hash256) (blocks:bytes_blocks) =
  update_multi SHA2_256 hash () blocks

let word_to_nat32 = vv
let nat32_to_word = to_uint32

let make_ordered_hash_def (abcd efgh:quad32) :
  (hash:words_state SHA2_256 {
         length hash == 8 /\
         hash.[0] == to_uint32 abcd.lo0 /\
         hash.[1] == to_uint32 abcd.lo1 /\
         hash.[2] == to_uint32 abcd.hi2 /\
         hash.[3] == to_uint32 abcd.hi3 /\
         hash.[4] == to_uint32 efgh.lo0 /\
         hash.[5] == to_uint32 efgh.lo1 /\
         hash.[6] == to_uint32 efgh.hi2 /\
         hash.[7] == to_uint32 efgh.hi3
   })
  =
    let a = to_uint32 abcd.lo0 in
    let b = to_uint32 abcd.lo1 in
    let c = to_uint32 abcd.hi2 in
    let d = to_uint32 abcd.hi3 in
    let e = to_uint32 efgh.lo0 in
    let f = to_uint32 efgh.lo1 in
    let g = to_uint32 efgh.hi2 in
    let h = to_uint32 efgh.hi3 in
    let l = [a; b; c; d; e; f; g; h] in
    let hash = seq_of_list l in
    assert_norm (length hash == 8);
    elim_of_list l;
    hash
[@"opaque_to_smt"] let make_ordered_hash = opaque_make make_ordered_hash_def
irreducible let make_ordered_hash_reveal = opaque_revealer (`%make_ordered_hash) make_ordered_hash make_ordered_hash_def

let shuffle_core_properties (block:block_w) (hash:hash256) (t:counter{t < size_k_w_256}) :
    Lemma(let h = shuffle_core_opaque block hash t in
          let open Lib.IntTypes in
          let a0 = hash.[0] in
          let b0 = hash.[1] in
          let c0 = hash.[2] in
          let d0 = hash.[3] in
          let e0 = hash.[4] in
          let f0 = hash.[5] in
          let g0 = hash.[6] in
          let h0 = hash.[7] in
          let t1 = h0 +. (_Sigma1 SHA2_256 e0) +. (_Ch SHA2_256 e0 f0 g0) +. (k0 SHA2_256).[t] +. (ws SHA2_256 block t) in
          let t2 = (_Sigma0 SHA2_256 a0) +. (_Maj SHA2_256 a0 b0 c0) in
          h.[0] == t1 +. t2 /\
          h.[1] == a0 /\
          h.[2] == b0 /\
          h.[3] == c0 /\
          h.[4] == d0 +. t1 /\
          h.[5] == e0 /\
          h.[6] == f0 /\
          h.[7] == g0)
  =
  Pervasives.reveal_opaque (`%shuffle_core) shuffle_core;
  let h = shuffle_core SHA2_256 block hash t in
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in
  let t1 = h0 +. (_Sigma1 SHA2_256 e0) +. (_Ch SHA2_256 e0 f0 g0) +. (k0 SHA2_256).[t] +. (ws SHA2_256 block t) in
  let t2 = (_Sigma0 SHA2_256 a0) +. (_Maj SHA2_256 a0 b0 c0) in
  let l = [ t1 +. t2; a0; b0; c0; d0 +. t1; e0; f0; g0 ] in
  assert (h == seq_of_list l);
  elim_of_list l;
  ()

let lemma_add_wrap_is_add_mod (n0 n1:nat32) :
  Lemma (add_wrap n0 n1 == vv (add_mod (to_uint32 n0) (to_uint32 n1)))
  =
  assert_norm (pow2 32 == pow2_32);
  ()

unfold let shuffle_opaque = shuffle

let update_block (hash:hash256) (block:block_w): Tot (hash256) =
  let hash_1 = shuffle_opaque SHA2_256 hash block in
  let open Lib.IntTypes in
  Spec.Loops.seq_map2 ( +. ) hash hash_1

#push-options "--z3cliopt smt.arith.nl=true" (* FIXME: Seemingly needed after fix to #2894 in F*, but should not be *)
let lemma_update_block_equiv (hash:hash256) (block:bytes{length block = block_length}) :
  Lemma (update_block hash (words_of_bytes SHA2_256 #(block_word_length SHA2_256) block) == update SHA2_256 hash block)
  =
  Pervasives.reveal_opaque (`%Spec.SHA2.update) Spec.SHA2.update;
  Pervasives.reveal_opaque (`%Spec.SHA2.shuffle) Spec.SHA2.shuffle;
  assert (equal (update_block hash (words_of_bytes SHA2_256 #(block_word_length SHA2_256) block)) (update SHA2_256 hash block));
  ()
#pop-options

let update_multi_one (h:hash256) (b:bytes_blocks {length b = block_length}) : Lemma
  (ensures (update_multi SHA2_256 h () b == update SHA2_256 h b)) =
  update_multi_update SHA2_256 h b

friend Lib.ByteSequence

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0 --z3cliopt smt.arith.nl=true"
let lemma_be_to_n_4 (s:seq4 nat8) : Lemma
  (Lib.ByteSequence.nat_from_bytes_be #Lib.IntTypes.SEC (seq_nat8_to_seq_uint8 s) == be_bytes_to_nat32 s)
  =
  let open Lib.IntTypes in
  let open Vale.Def.Words.Four_s in
  assert (pow2 8 = 0x100);
  assert (pow2 16 = 0x10000);
  assert_norm (pow2 24 = 0x1000000);
  let x = seq_nat8_to_seq_uint8 s in
  let f = Lib.ByteSequence.nat_from_intseq_be_ #U8 #SEC in
  calc (==) {
    f x <: nat ;
    == { }
    FStar.UInt8.v (last x) + pow2 8 * f (slice x 0 3);
    == {}
    index s 3 + pow2 8 * f (slice x 0 3);
    == {}
    index s 3 + pow2 8 * index s 2 + pow2 16 * f (slice x 0 2);
    == {}
    index s 3 + pow2 8 * index s 2 + pow2 16 * index s 1 + pow2 24 * f (slice x 0 1);
    == {}
    index s 3 + pow2 8 * index s 2 + pow2 16 * index s 1 + pow2 24 * index s 0 + pow2 32 * f (slice x 0 0);
    == {}
    index s 3 + pow2 8 * index s 2 + pow2 16 * index s 1 + pow2 24 * index s 0;
    == {}
    four_to_nat_unfold 8 (seq_to_four_BE s);
    == {reveal_opaque (`%four_to_nat) four_to_nat}
    be_bytes_to_nat32 s;
  }

let lemma_mod_transform (quads:seq quad32) : Lemma
  (requires length quads % 4 == 0)
  (ensures length (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes quads)) % 64 == 0)
  =
  ()

let lemma_update_multi_opaque_vale_is_update_multi (hash:hash256) (blocks:bytes) : Lemma
  (requires length blocks % 64 = 0)
  (ensures  update_multi_opaque_vale hash blocks == update_multi_transparent hash blocks)
  =
  update_multi_reveal ();
  ()

let sigma_0_0_partial_def (t:counter) (block:block_w) : nat32 =
    if 16 <= t && t < size_k_w_256 then
       (let sigma0_in = ws_opaque block (t-15) in
        sigma256_0_0 sigma0_in)
    else
       0

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 30"
let lemma_sha256_sigma0 (src:quad32) (t:counter) (block:block_w) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256) /\
            src.hi3 == ws_opaque block (t-15))
  (ensures (sigma256_0_0 src.hi3 == sigma_0_0_partial t block))
  =
  sigma_0_0_partial_reveal ();
  ()
#reset-options "--max_fuel 0 --max_ifuel 0"

let sigma_0_1_partial_def (t:counter) (block:block_w) : nat32 =
    if 16 <= t && t < size_k_w_256 then
       (let sigma1_in = ws_opaque block (t-2) in
        sigma256_0_1 sigma1_in)
    else
       0

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 30"
let lemma_sha256_sigma1 (src:quad32) (t:counter) (block:block_w) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256) /\
            src.hi3 == ws_opaque block (t-2))
  (ensures (sigma256_0_1 src.hi3 == sigma_0_1_partial t block))
  =
  sigma_0_1_partial_reveal ();
  ()
#reset-options "--max_fuel 0 --max_ifuel 0"

let sigma_1_0_partial_def (t:counter) (block:block_w) (hash_orig:hash256) : nat32 =
    if t < size_k_w_256 then
       (let sigma0_in = word_to_nat32 ((repeat_range_vale t block hash_orig).[0]) in
        sigma256_1_0 sigma0_in)
    else
       0

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 30"
let lemma_sha256_sigma2 (src:quad32) (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w(SHA2_256) /\
            src.hi3 == word_to_nat32 ((repeat_range_vale t block hash_orig).[0]))
  (ensures (sigma256_1_0 src.hi3 == sigma_1_0_partial t block hash_orig))
  =
  sigma_1_0_partial_reveal ();
  ()
#reset-options "--max_fuel 0 --max_ifuel 0"

let sigma_1_1_partial_def (t:counter) (block:block_w) (hash_orig:hash256) : nat32 =
    if t < size_k_w_256 then
       (let sigma1_in = word_to_nat32 ((repeat_range_vale t block hash_orig).[4]) in
        sigma256_1_1 sigma1_in)
    else
       0

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 30"
let lemma_sha256_sigma3 (src:quad32) (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w(SHA2_256) /\
            src.hi3 == word_to_nat32 ((repeat_range_vale t block hash_orig).[4]))
  (ensures (sigma256_1_1 src.hi3 == sigma_1_1_partial t block hash_orig))
  =
  sigma_1_1_partial_reveal ();
  ()
#reset-options "--max_fuel 0 --max_ifuel 0"

let make_seperated_hash_def (a b c d e f g h:nat32) :
  (hash:words_state SHA2_256 {
         length hash == 8 /\
         hash.[0] == to_uint32 a /\
         hash.[1] == to_uint32 b /\
         hash.[2] == to_uint32 c /\
         hash.[3] == to_uint32 d /\
         hash.[4] == to_uint32 e /\
         hash.[5] == to_uint32 f /\
         hash.[6] == to_uint32 g /\
         hash.[7] == to_uint32 h
   })
  =
    let a = to_uint32 a in
    let b = to_uint32 b in
    let c = to_uint32 c in
    let d = to_uint32 d in
    let e = to_uint32 e in
    let f = to_uint32 f in
    let g = to_uint32 g in
    let h = to_uint32 h in
    let l = [a; b; c; d; e; f; g; h] in
    let hash = seq_of_list l in
    assert_norm (length hash == 8);
    elim_of_list l;
    hash
[@"opaque_to_smt"] let make_seperated_hash = opaque_make make_seperated_hash_def
irreducible let make_seperated_hash_reveal = opaque_revealer (`%make_seperated_hash) make_seperated_hash make_seperated_hash_def

let make_seperated_hash_quad32_def (a b c d e f g h:quad32) :
  (hash:words_state SHA2_256 {
         length hash == 8 /\
         hash.[0] == to_uint32 a.hi3 /\
         hash.[1] == to_uint32 b.hi3 /\
         hash.[2] == to_uint32 c.hi3 /\
         hash.[3] == to_uint32 d.hi3 /\
         hash.[4] == to_uint32 e.hi3 /\
         hash.[5] == to_uint32 f.hi3 /\
         hash.[6] == to_uint32 g.hi3 /\
         hash.[7] == to_uint32 h.hi3
   })
  =
    let a = to_uint32 a.hi3 in
    let b = to_uint32 b.hi3 in
    let c = to_uint32 c.hi3 in
    let d = to_uint32 d.hi3 in
    let e = to_uint32 e.hi3 in
    let f = to_uint32 f.hi3 in
    let g = to_uint32 g.hi3 in
    let h = to_uint32 h.hi3 in
    let l = [a; b; c; d; e; f; g; h] in
    let hash = seq_of_list l in
    assert_norm (length hash == 8);
    elim_of_list l;
    hash
[@"opaque_to_smt"] let make_seperated_hash_quad32 = opaque_make make_seperated_hash_quad32_def
irreducible let make_seperated_hash_quad32_reveal = opaque_revealer (`%make_seperated_hash_quad32) make_seperated_hash_quad32 make_seperated_hash_quad32_def

let lemma_make_seperated_hash (hash:hash256) (a b c d e f g h:quad32) : Lemma
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
  =
  assert (equal hash (make_seperated_hash_quad32 a b c d e f g h))

let lemma_vsel32 (a b c:nat32) : Lemma
  (ensures (isel32 a b c = (iand32 c a) *^ (iand32 (inot32 c) b)))
  =
  reveal_iand_all 32;
  reveal_inot_all 32;
  reveal_ixor_all 32;
  lemma_equal_nth 32 (isel32 a b c) ((iand32 c a) *^ (iand32 (inot32 c) b))

let ch_256_def (x y z:nat32) :
  (a:nat32 {a == (iand32 x y) *^ (iand32 (inot32 x) z)})
  =
  reveal_iand_all 32;
  reveal_inot_all 32;
  reveal_ixor_all 32;
  ch256 x y z
[@"opaque_to_smt"] let ch_256 = opaque_make ch_256_def
irreducible let ch_256_reveal = opaque_revealer (`%ch_256) ch_256 ch_256_def

let lemma_eq_maj_xvsel32 (a b c:nat32) : Lemma
  (ensures (isel32 c b (a *^ b) = (iand32 a b) *^ ((iand32 a c) *^ (iand32 b c))))
  =
  reveal_iand_all 32;
  reveal_ixor_all 32;
  lemma_equal_nth 32 (isel32 c b (a *^ b)) ((iand32 a b) *^ ((iand32 a c) *^ (iand32 b c)))

let maj_256_def (x y z:nat32) :
  (a:nat32 {a == (iand32 x y) *^ ((iand32 x z) *^ (iand32 y z))})
  =
  reveal_iand_all 32;
  reveal_ixor_all 32;
  maj256 x y z
[@"opaque_to_smt"] let maj_256 = opaque_make maj_256_def
irreducible let maj_256_reveal = opaque_revealer (`%maj_256) maj_256 maj_256_def

let lemma_sigma_0_0_partial (t:counter) (block:block_w) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256))
  (ensures (sigma256_0_0 (ws_opaque block (t-15)) == sigma_0_0_partial t block))
  =
  sigma_0_0_partial_reveal ()

let lemma_sigma_0_1_partial (t:counter) (block:block_w) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256))
  (ensures (sigma256_0_1 (ws_opaque block (t-2)) == sigma_0_1_partial t block))
  =
  sigma_0_1_partial_reveal ()

let lemma_sigma_1_0_partial (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w(SHA2_256))
  (ensures (sigma256_1_0 (word_to_nat32 ((repeat_range_vale t block hash_orig).[0])) == sigma_1_0_partial t block hash_orig))
  =
  sigma_1_0_partial_reveal ()

let lemma_sigma_1_1_partial (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
  (requires t < size_k_w(SHA2_256))
  (ensures (sigma256_1_1 (word_to_nat32 ((repeat_range_vale t block hash_orig).[4])) == sigma_1_1_partial t block hash_orig))
  =
  sigma_1_1_partial_reveal ()

#reset-options "--z3rlimit 20 --max_fuel 1"
let lemma_quads_to_block_be qs
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #nat32);
  reveal_opaque (`%ws) ws
#reset-options "--max_fuel 0 --max_ifuel 0"

#reset-options "--z3rlimit 20"
let lemma_shuffle_core_properties (t:counter) (block:block_w) (hash_orig:hash256) : Lemma
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
  =
  let hash = Spec.Loops.repeat_range 0 t (shuffle_core_opaque block) hash_orig in
  let a0 = word_to_nat32 hash.[0] in
  let b0 = word_to_nat32 hash.[1] in
  let c0 = word_to_nat32 hash.[2] in
  let d0 = word_to_nat32 hash.[3] in
  let e0 = word_to_nat32 hash.[4] in
  let f0 = word_to_nat32 hash.[5] in
  let g0 = word_to_nat32 hash.[6] in
  let h0 = word_to_nat32 hash.[7] in
  ch_256_reveal ();
  maj_256_reveal ();
  lemma_add_wrap_is_add_mod h0 (sigma256_1_1 e0);
  lemma_add_wrap_is_add_mod (add_wrap h0 (sigma256_1_1 e0)) (ch_256 e0 f0 g0);
  lemma_add_wrap_is_add_mod (add_wrap (add_wrap h0 (sigma256_1_1 e0)) (ch_256 e0 f0 g0)) (word_to_nat32 k.[t]);
  lemma_add_wrap_is_add_mod (add_wrap (add_wrap (add_wrap h0 (sigma256_1_1 e0)) (ch_256 e0 f0 g0)) (word_to_nat32 k.[t])) (ws_opaque block t);
  lemma_add_wrap_is_add_mod (sigma256_1_0 a0) (maj_256 a0 b0 c0);
  lemma_add_wrap_is_add_mod (add_wrap (add_wrap (add_wrap (add_wrap h0 (sigma256_1_1 e0)) (ch_256 e0 f0 g0)) (word_to_nat32 k.[t])) (ws_opaque block t)) (add_wrap (sigma256_1_0 a0) (maj_256 a0 b0 c0));
  lemma_add_wrap_is_add_mod d0 (add_wrap (add_wrap (add_wrap (add_wrap h0 (sigma256_1_1 e0)) (ch_256 e0 f0 g0)) (word_to_nat32 k.[t])) (ws_opaque block t));
  Spec.Loops.repeat_range_induction 0 (t + 1) (shuffle_core_opaque block) hash_orig;
  shuffle_core_properties block (Spec.Loops.repeat_range 0 t (shuffle_core_opaque block) hash_orig) t
#reset-options "--max_fuel 0 --max_ifuel 0"

let lemma_add_mod_commutes (x y:UInt32.t) :
  Lemma (add_mod x y == add_mod y x)
  =
  ()

let lemma_add_mod_associates_U32 (x y z:UInt32.t) :
  Lemma (add_mod x (add_mod y z) == add_mod (add_mod x y) z)
  =
  let open Lib.IntTypes in
  calc (==) {
    v (x +. (y +. z));
    (==) { }
    (v x + (v y + v z) % pow2 32) % pow2 32;
    (==) { FStar.Math.Lemmas.lemma_mod_add_distr (v x) (v y + v z) (pow2 32) }
    ((v x + v y) + v z) % pow2 32;
    (==) { FStar.Math.Lemmas.lemma_mod_add_distr (v z) (v x + v y) (pow2 32) }
    ((v x + v y) % pow2 32 + v z) % pow2 32;
    (==) { }
    v ((x +. y) +. z);
  };
  v_inj (x +. (y +. z)) ((x +. y) +. z)

let lemma_add_mod_ws_rearrangement (a b c d:UInt32.t) :
  Lemma (let open Lib.IntTypes in
    a +. b +. c +. d == d +. c +. b +. a)
  =
  let open Lib.IntTypes in
  calc (==) {
    a +. b +. c +. d;
    (==) {}
    (((a +. b) +. c) +. d);
    (==) {   lemma_add_mod_commutes ((a +. b) +. c) d;
             lemma_add_mod_commutes (a +. b) c;
             lemma_add_mod_commutes a b
         }
    d +. (c +. (b +. a));
    (==) { lemma_add_mod_associates_U32 d c (b +. a);
           lemma_add_mod_associates_U32 (d +. c) b a}
    (((d +. c) +. b) +. a);
  }

#reset-options "--fuel 1 --z3rlimit 50"
let lemma_ws_opaque (block:block_w) (t:counter) : Lemma
  (requires 16 <= t && t < size_k_w_256)
  (ensures (let sigma0 = sigma256_0_0 (ws_opaque block (t - 15)) in
            let sigma1 = sigma256_0_1 (ws_opaque block (t - 2)) in
            ws_opaque block t == add_wrap (add_wrap (add_wrap sigma1 (ws_opaque block (t - 7))) sigma0) (ws_opaque block (t - 16))))
  =
  let t16 = ws SHA2_256 block (t - 16) in
  let t15 = ws SHA2_256 block (t - 15) in
  let t7  = ws SHA2_256 block (t - 7) in
  let t2  = ws SHA2_256 block (t - 2) in
  let sigma0 = sigma256_0_0 (ws_opaque block (t - 15)) in
  let sigma1 = sigma256_0_1 (ws_opaque block (t - 2)) in
  let s1 = _sigma1 SHA2_256 t2 in
  let s0 = _sigma0 SHA2_256 t15 in
  calc (==) {
    ws_opaque block t;
    (==) { Pervasives.reveal_opaque (`%ws) ws }
    vv ((s1 +. t7 +. s0) +. t16);
    (==) { lemma_add_wrap_is_add_mod (vv (s1 +. t7 +. s0)) (ws_opaque block (t-16)) }
    add_wrap (vv ((s1 +. t7) +. s0)) (ws_opaque block (t-16));
    (==) { lemma_add_wrap_is_add_mod (vv (s1 +. t7)) sigma0 }
    add_wrap (add_wrap (vv (s1 +. t7)) sigma0) (ws_opaque block (t-16));
    (==) { lemma_add_wrap_is_add_mod sigma1 (ws_opaque block (t-7)) }
    add_wrap (add_wrap (add_wrap sigma1 (ws_opaque block (t - 7))) sigma0) (ws_opaque block (t - 16));

  }

#reset-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let translate_hash_update (a b c d e f g h a' b' c' d' e' f' g' h' a_old b_old c_old d_old e_old f_old g_old h_old:quad32) : Lemma
  (requires a' == add_wrap_quad32 a a_old /\
            b' == add_wrap_quad32 b b_old /\
            c' == add_wrap_quad32 c c_old /\
            d' == add_wrap_quad32 d d_old /\
            e' == add_wrap_quad32 e e_old /\
            f' == add_wrap_quad32 f f_old /\
            g' == add_wrap_quad32 g g_old /\
            h' == add_wrap_quad32 h h_old)
  (ensures (
         let h = make_seperated_hash_quad32 a b c d e f g h in
         let a = make_seperated_hash_quad32 a_old b_old c_old d_old e_old f_old g_old h_old in
         let h' = make_seperated_hash_quad32 a' b' c' d' e' f' g' h' in
         let open Lib.IntTypes in
         let mapped = Spec.Loops.seq_map2 ( +. ) h a in
         mapped == h'))
  =
  let h = make_seperated_hash_quad32 a b c d e f g h in
  let a = make_seperated_hash_quad32 a_old b_old c_old d_old e_old f_old g_old h_old in
  let h' = make_seperated_hash_quad32 a' b' c' d' e' f' g' h' in
  let open Lib.IntTypes in
  let mapped = Spec.Loops.seq_map2 ( +. ) h a in
  FStar.Classical.forall_intro_2 lemma_add_wrap_is_add_mod;
  assert (equal mapped h');
  ()

let update_lemma (a b c d e f g h a_old b_old c_old d_old e_old f_old g_old h_old a' b' c' d' e' f' g' h':quad32) (block:block_w) : Lemma
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
  =
  let hash_orig = make_seperated_hash_quad32 a_old b_old c_old d_old e_old f_old g_old h_old in
  let hash_1 = shuffle_opaque SHA2_256 hash_orig block in
  Pervasives.reveal_opaque (`%shuffle) shuffle;
  Pervasives.reveal_opaque (`%shuffle_core) shuffle_core;
  let rec r (i:nat{i <= 64}) : Lemma (
    Spec.Loops.repeat_range 0 i (shuffle_core_opaque block) hash_orig ==
    Spec.Loops.repeat_range 0 i (shuffle_core SHA2_256 block) hash_orig)
    =
    if i = 0 then (
      Spec.Loops.repeat_range_base 0 (shuffle_core_opaque block) hash_orig;
      Spec.Loops.repeat_range_base 0 (shuffle_core SHA2_256 block) hash_orig
    ) else (
      r (i - 1);
      Spec.Loops.repeat_range_induction 0 i (shuffle_core_opaque block) hash_orig;
      Spec.Loops.repeat_range_induction 0 i (shuffle_core SHA2_256 block) hash_orig
    )
  in
  r 64;
  translate_hash_update a b c d e f g h a' b' c' d' e' f' g' h' a_old b_old c_old d_old e_old f_old g_old h_old;
  shuffle_is_shuffle_pre SHA2_256 hash_orig block;
  assert (equal (make_seperated_hash_quad32 a' b' c' d' e' f' g' h') (update_block hash_orig block));
  ()

#push-options "--max_fuel 1"
let lemma_slice_commutes_reverse_bytes_quad32_seq (s:seq quad32) (pivot:nat) : Lemma
  (requires pivot <= length s)
  (ensures  slice (reverse_bytes_quad32_seq s) 0 pivot == reverse_bytes_quad32_seq (slice s 0 pivot))
  =
  let rs = reverse_bytes_quad32_seq s in
  let srs = slice (reverse_bytes_quad32_seq s) 0 pivot in
  let ss = slice s 0 pivot in
  let rss = reverse_bytes_quad32_seq ss in
  if pivot = 0 then (
    assert (equal ss empty);
    assert (equal srs empty);
    assert (equal empty (reverse_bytes_quad32_seq empty));
    ()
  ) else (
    assert (equal srs rss)
  )

let lemma_update_multi_quads (s:seq quad32) (hash_orig:hash256) (bound:nat) : Lemma
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
  =
  let prefix_LE = slice s 0 bound in
  let prefix_BE = reverse_bytes_quad32_seq prefix_LE in
  let h_prefix = update_multi_quads prefix_BE hash_orig in
  let block_quads_LE = slice s bound (bound + 4) in
  let block_quads_BE = reverse_bytes_quad32_seq block_quads_LE in
  let input_LE = slice s 0 (bound+4) in
  let input_BE = reverse_bytes_quad32_seq input_LE in
  let h = update_block h_prefix (quads_to_block_be block_quads_BE) in
  lemma_slice_commutes_reverse_bytes_quad32_seq s bound;
  lemma_slice_commutes_reverse_bytes_quad32_seq s (bound + 4);
  assert (prefix_BE == slice (reverse_bytes_quad32_seq s) 0 bound);
  assert (input_BE == slice (reverse_bytes_quad32_seq s) 0 (bound + 4));
  if bound = 0 then ()
  else (
    let prefix, qs = split input_BE (length input_BE - 4) in
    assert (equal prefix prefix_BE);
    assert (equal qs block_quads_BE);
    ()
  )
#pop-options

#push-options "--max_fuel 1"
// One level of expansion that we can use in places that can't use fuel
let lemma_update_multi_quads_unfold (s:seq quad32) (hash_orig:hash256) : Lemma
  (requires length s >= 4)
  (ensures  (let prefix, qs = split s (length s - 4) in
             let h_prefix = update_multi_quads prefix hash_orig in
             let hash = update_block h_prefix (quads_to_block_be qs) in
             update_multi_quads s hash_orig == hash))
  =
  ()

let lemma_update_multi_quads_short (s:seq quad32) (hash_orig:hash256) : Lemma
  (requires length s < 4)
  (ensures  update_multi_quads s hash_orig == hash_orig)
  =
  ()
#pop-options

let lemma_le_bytes_to_hash_quads_part1 (s:seq quad32) : Lemma
  (requires length s == 2)
  (ensures  le_bytes_to_hash (le_seq_quad32_to_bytes s) ==
            Vale.Lib.Seqs_s.seq_map nat32_to_word (Vale.Def.Words.Seq_s.seq_four_to_seq_LE s))
  =
  let lhs = le_bytes_to_hash (le_seq_quad32_to_bytes s) in
  assert (lhs == Vale.Lib.Seqs_s.seq_map nat32_to_word (Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE (le_seq_quad32_to_bytes s)));
  le_seq_quad32_to_bytes_reveal ();
  Vale.Def.Words.Seq.seq_nat8_to_seq_nat32_to_seq_nat8_LE (Vale.Def.Words.Seq_s.seq_four_to_seq_LE s);
  ()

#push-options "--z3rlimit 30"
let lemma_le_bytes_to_hash_quads (s:seq quad32) : Lemma
  (requires length s == 2)
  (ensures (let rhs = le_bytes_to_hash (le_seq_quad32_to_bytes s) in
            rhs.[0] == to_uint32 (s.[0]).lo0 /\
            rhs.[1] == to_uint32 (s.[0]).lo1 /\
            rhs.[2] == to_uint32 (s.[0]).hi2 /\
            rhs.[3] == to_uint32 (s.[0]).hi3 /\
            rhs.[4] == to_uint32 (s.[1]).lo0 /\
            rhs.[5] == to_uint32 (s.[1]).lo1 /\
            rhs.[6] == to_uint32 (s.[1]).hi2 /\
            rhs.[7] == to_uint32 (s.[1]).hi3 /\
            length rhs == 8))
  =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat32);
  let rhs = le_bytes_to_hash (le_seq_quad32_to_bytes s) in
  lemma_le_bytes_to_hash_quads_part1 s;
  assert (rhs == Vale.Lib.Seqs_s.seq_map nat32_to_word (Vale.Def.Words.Seq_s.seq_four_to_seq_LE s));
  ()
#pop-options

let lemma_hash_to_bytes (s:seq quad32) : Lemma
  (requires length s == 2)
  (ensures make_ordered_hash s.[0] s.[1] == le_bytes_to_hash (le_seq_quad32_to_bytes s))
  =
  lemma_le_bytes_to_hash_quads s;
  assert (equal (make_ordered_hash s.[0] s.[1]) (le_bytes_to_hash (le_seq_quad32_to_bytes s)));
  ()

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 40"

let lemma_endian_relation (quads qs:seq quad32) (input2:seq UInt8.t) : Lemma
  (requires length qs == 4 /\ length input2 == 64 /\
            qs == reverse_bytes_quad32_seq quads /\
            input2 == seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes quads))
  (ensures  quads_to_block_be qs == words_of_bytes SHA2_256 #(block_word_length SHA2_256) input2)
  =
  let fi (i:nat{i < length (quads_to_block_be qs)}) : Lemma
    ((quads_to_block_be qs).[i] == (words_of_bytes SHA2_256 #(block_word_length SHA2_256) input2).[i])
    =
    let open Vale.Def.Words.Four_s in
    let open Vale.Lib.Seqs_s in
    let ni = (seq_four_to_seq_LE quads).[i] in
    let b = slice input2 (4 * i) (4 * i + 4) in
    calc (==) {
      b;
      == {}
      slice input2 (4 * i) (4 * i + 4);
      == {}
      slice (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes quads)) (4 * i) (4 * i + 4);
      == {le_seq_quad32_to_bytes_reveal ()}
      slice (seq_nat8_to_seq_uint8 (seq_nat32_to_seq_nat8_LE (seq_four_to_seq_LE quads))) (4 * i) (4 * i + 4);
      equal {}
      seq_nat8_to_seq_uint8 (slice (seq_nat32_to_seq_nat8_LE (seq_four_to_seq_LE quads)) (4 * i) (4 * i + 4));
      == {}
      seq_nat8_to_seq_uint8 (slice (seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE quads))) (4 * i) (4 * i + 4));
      == {slice_commutes_seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE quads)) i (i + 1)}
      seq_nat8_to_seq_uint8 (seq_four_to_seq_LE (slice (seq_map (nat_to_four 8) (seq_four_to_seq_LE quads)) i (i + 1)));
      equal {reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat8)}
      seq_nat8_to_seq_uint8 (four_to_seq_LE (nat_to_four 8 (seq_four_to_seq_LE quads).[i]));
    };
    let open Lib.IntTypes in
    calc (==) {
      (words_of_bytes SHA2_256 #(block_word_length SHA2_256) input2).[i];
      == { }
      (Lib.ByteSequence.uints_from_bytes_be #U32 #SEC #(block_word_length SHA2_256) input2).[i];
      == { Lib.ByteSequence.index_uints_from_bytes_be #U32 #SEC #(block_word_length SHA2_256) input2 i }
      Lib.ByteSequence.uint_from_bytes_be (Lib.Sequence.sub #uint8 #64 input2 (i * 4) 4);
      == { let open Lib.Sequence in
           calc (==) {
             sub #uint8 #64 input2 (i * 4) 4;
             == {  }
             Seq.slice input2 (4 * i) (4 * i + 4);
           }
         }
      Lib.ByteSequence.uint_from_bytes_be #U32 #SEC b;
      == { calc (==) {
             Lib.ByteSequence.nat_from_bytes_be #SEC b;
             (==) { }
             Lib.ByteSequence.nat_from_bytes_be #SEC (seq_nat8_to_seq_uint8 (four_to_seq_LE (nat_to_four 8 ni)));
             (==) { lemma_be_to_n_4 (four_to_seq_LE (nat_to_four 8 ni)) }
             be_bytes_to_nat32 (four_to_seq_LE (nat_to_four 8 ni));
           };
           v_inj (Lib.ByteSequence.uint_from_bytes_be #U32 #SEC b)
             (u32 (be_bytes_to_nat32 (four_to_seq_LE (nat_to_four 8 ni))))
         }
      nat32_to_word (be_bytes_to_nat32 (four_to_seq_LE (nat_to_four 8 ni)));
      == {}
      nat32_to_word (be_bytes_to_nat32 (reverse_seq (nat32_to_be_bytes ni)));
      == {reverse_bytes_nat32_reveal ()}
      nat32_to_word (reverse_bytes_nat32 ni);
      == {}
      nat32_to_word (reverse_bytes_nat32 (seq_four_to_seq_LE quads).[i]);
      == {reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat32); reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #nat32); reveal_reverse_bytes_quad32 quads.[(i / 4)]}
      nat32_to_word (seq_four_to_seq_BE qs).[i];
      == {}
      (quads_to_block_be qs).[i];
    }
    in
  FStar.Classical.forall_intro fi;
  assert (equal (quads_to_block_be qs) (words_of_bytes SHA2_256 #(block_word_length SHA2_256) input2))

#reset-options "--max_fuel 0 --ifuel 1 --z3rlimit 20"
let rec lemma_update_multi_equiv_vale (hash hash':hash256) (quads:seq quad32) (r_quads:seq quad32)
  (nat8s:seq nat8) (blocks:seq UInt8.t) :
  Lemma (requires length quads % 4 == 0 /\
                  r_quads == reverse_bytes_quad32_seq quads /\
                  nat8s == le_seq_quad32_to_bytes quads /\
                  blocks == seq_nat8_to_seq_uint8 nat8s /\
                  hash' == update_multi_quads r_quads hash)
        (ensures
           length blocks % 64 == 0 /\
           hash' == update_multi_opaque_vale hash blocks)
        (decreases (length quads))
  =
  lemma_mod_transform quads;
  assert (length blocks % 64 == 0);
  update_multi_reveal ();
  if length quads = 0 then begin
    lemma_le_seq_quad32_to_bytes_length quads;
    lemma_update_multi_quads_short r_quads hash;
    assert (equal blocks empty);
    update_multi_zero SHA2_256 hash;
    ()
  end else begin
    let num_blocks = (length quads) / 4 in
    let bytes_pivot = (num_blocks - 1) * 64 in

    // Use associativity of update_multi to rearrange recursion to better match update_multi_quads' recursion
    let input1,input2 = Lib.UpdateMulti.split_block block_length blocks (bytes_pivot / 64) in

    let h_bytes1 = update_multi SHA2_256 hash () input1 in
    let h_bytes2 = update_multi SHA2_256 h_bytes1 () input2 in
    update_multi_associative SHA2_256 hash input1 input2;
    assert (input1 `Seq.append` input2 == blocks);
    Seq.lemma_eq_intro h_bytes2 (update_multi SHA2_256 hash () blocks);
    assert (h_bytes2 == update_multi SHA2_256 hash () blocks);

    // Unfold update_multi_quads one level, so we can start matching parts up
    let prefix, qs = split r_quads (length r_quads - 4) in
    let h_prefix = update_multi_quads prefix hash in
    let h_final = update_block h_prefix (quads_to_block_be qs) in
    lemma_update_multi_quads_unfold r_quads hash;

    (* Step 1: Show that h_prefix == h_bytes1 *)

    let r_prefix = reverse_bytes_quad32_seq prefix in
    lemma_update_multi_equiv_vale hash h_prefix r_prefix prefix
                             (le_seq_quad32_to_bytes r_prefix)
                             (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes r_prefix));
    assert (h_prefix == update_multi SHA2_256 hash () (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes r_prefix)));
    assert (equal (slice (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes quads)) 0 bytes_pivot)
                  (seq_nat8_to_seq_uint8 (slice (le_seq_quad32_to_bytes quads) 0 bytes_pivot)));
    slice_commutes_le_seq_quad32_to_bytes0 quads (bytes_pivot / 16);
    assert (bytes_pivot / 16 == length quads - 4);
    assert (reverse_bytes_quad32_seq (reverse_bytes_quad32_seq (slice quads 0 (length quads - 4))) == slice quads 0 (length quads - 4));
    Vale.Lib.Seqs.slice_seq_map_commute reverse_bytes_quad32 quads 0 (length quads - 4);
    assert (Seq.equal h_prefix h_bytes1);  // Conclusion of Step 1
    Vale.Lib.Seqs.slice_seq_map_commute reverse_bytes_quad32 quads (length quads - 4) (length quads);
    slice_commutes_le_seq_quad32_to_bytes quads (bytes_pivot/16) ((length blocks)/16);

    (* Step 2: Show that update_block SHA2_256 h_prefix (quads_to_block qs) == update_multi SHA2_256 h_bytes1 input2 *)

    assert (equal input2 (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (slice quads (length quads - 4) (length quads)))));
    lemma_endian_relation (slice quads (length quads - 4) (length quads)) qs
                          input2;  // ==> quads_to_block qs == words_of_bytes SHA2_256 (block_word_length SHA2_256) input2
    lemma_update_block_equiv h_bytes1 input2;
    update_multi_one h_bytes1 input2;
    ()
  end
