module Vale.AES.AES_helpers_BE

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Seq
open Vale.AES.AES_BE_s
open FStar.Mul

#reset-options "--fuel 4 --ifuel 0"
let lemma_expand_key_128_0 (key:aes_key_word AES_128) =
  expand_key_reveal ()

#reset-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let lemma_expand_key_128_i (key:aes_key_word AES_128) (i:nat) =
  expand_key_reveal ();
  let n = 4 * i in
  // unfold expand_key 4 times (could use fuel, but that unfolds everything):
  let _ = expand_key AES_128 key (n + 1) in
  let _ = expand_key AES_128 key (n + 2) in
  let _ = expand_key AES_128 key (n + 3) in
  ()
#reset-options

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
let rec lemma_expand_append (key:aes_key_word AES_128) (size1:nat) (size2:nat) =
  expand_key_reveal ();
  if size1 < size2 then lemma_expand_append key size1 (size2 - 1)

#reset-options "--fuel 1 --ifuel 0 --z3rlimit 40 --using_facts_from '* -FStar.Seq.Properties'"
#restart-solver
// quad32 key expansion is equivalent to nat32 key expansion
let rec lemma_expand_key_128 (key:seq nat32) (size:nat) =
  expand_key_128_reveal ();
  lemma_expand_append key (4 * size) 44;
  if size = 0 then ()
  else
  (
    let i = size - 1 in
    lemma_expand_append key (4 * i) 44;
    lemma_expand_key_128 key i;
    if i = 0 then lemma_expand_key_128_0 key
    else lemma_expand_key_128_i key i
  )
#reset-options

// SIMD version of round_key_128 is equivalent to scalar round_key_128
#push-options "--fuel 3 --ifuel 3"  // REVIEW: Why do we need this?
let lemma_simd_round_key (prev:quad32) (rcon:nat32) =
  quad32_xor_reveal ();
  commute_rot_word_sub_word prev.lo0 rcon;
  Vale.Arch.Types.xor_lemmas ()
#pop-options

let init_rounds_opaque (init:quad32) (round_keys:seq quad32) =
  eval_rounds_reveal ()

#push-options "--ifuel 2"  // REVIEW: Why do we need this?  Extra inversion to deal with opaque?
let finish_cipher (alg:algorithm) (input:quad32) (round_keys:seq quad32) =
  eval_rounds_reveal ();
  eval_cipher_reveal ()

let finish_cipher_opt (alg:algorithm) (input plain t0 t1 out:quad32) (round_keys:seq quad32) : Lemma
  (requires length round_keys == (nr alg) + 1 /\
            length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
            t0 = quad32_xor input (index round_keys 0) /\
            t1 = eval_rounds t0 round_keys (nr alg - 1) /\
            out = quad32_xor (shift_rows (sub_bytes t1)) (quad32_xor plain (index round_keys (nr alg))))
  (ensures out == quad32_xor plain (eval_cipher alg input round_keys))
  =
  calc (==) {
    out;
    == {} // From requires
    quad32_xor (shift_rows (sub_bytes t1)) (quad32_xor plain (index round_keys (nr alg)));
    == { Vale.Arch.TypesNative.lemma_quad32_xor_commutes plain (index round_keys (nr alg)) }
    quad32_xor (shift_rows (sub_bytes t1)) (quad32_xor (index round_keys (nr alg)) plain);
    == { Vale.Arch.TypesNative.lemma_quad32_xor_associates (shift_rows (sub_bytes t1)) (index round_keys (nr alg)) plain }
    quad32_xor (quad32_xor (shift_rows (sub_bytes t1)) (index round_keys (nr alg))) plain;
    == { eval_rounds_reveal ();
         eval_cipher_reveal ();
         quad32_xor_reveal ()
       }
    quad32_xor (eval_cipher alg input round_keys) plain;
    == { Vale.Arch.TypesNative.lemma_quad32_xor_commutes plain (eval_cipher alg input round_keys) }
    quad32_xor plain (eval_cipher alg input round_keys);
  };
  ()
#pop-options
