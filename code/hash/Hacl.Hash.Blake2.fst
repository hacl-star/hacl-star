module Hacl.Hash.Blake2

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies
module S = FStar.Seq
module U32 = FStar.UInt32

open Lib.IntTypes

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

open Hacl.Hash.Lemmas
open Spec.Blake2.Lemmas

open FStar.Mul

#set-options "--fuel 0 --ifuel 0"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"

noextract inline_for_extraction
val mk_update_multi: a:hash_alg{is_blake a} -> update:update_st a -> update_multi_st a

let mk_update_multi a update s ev blocks n_blocks =
  let h0 = ST.get () in
  let inv (h: HS.mem) (i: nat) =
    let i_block = block_length a * i in
    let i_block' = block_length a * (i+1) in
    i <= U32.v n_blocks /\
    B.live h s /\ B.live h blocks /\
    B.(modifies (loc_buffer s) h0 h) /\
    (as_seq h s, add_extra_i a ev (U32.uint_to_t i)) ==
      (Spec.Agile.Hash.update_multi a (as_seq h0 s, ev) (S.slice (B.as_seq h0 blocks) 0 i_block))
  in
  let f (i:U32.t { U32.(0 <= v i /\ v i < v n_blocks)}): ST.Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
  =
    let h1 = ST.get () in
    let sz = block_len a in
    let blocks0 = B.sub blocks 0ul U32.(sz *^ i) in
    let block = B.sub blocks U32.(sz *^ i) sz in
    let v' = update s (add_extra_i a ev i) block in
    let h2 = ST.get () in
    let aux () : Lemma ((as_seq h2 s, v') ==
      Spec.Agile.Hash.update_multi a (as_seq h0 s, ev) (S.slice (B.as_seq h0 blocks) 0 (block_length a * (U32.v i + 1))) /\
      v' == add_extra_i a ev (U32.uint_to_t (U32.v i + 1))
      )
    = let s0 = as_seq h0 s in
      let s1 = as_seq h1 s in
      let blocks = B.as_seq h0 blocks in
      let block = B.as_seq h0 block in
      let i = U32.v i in
      let i_block = block_length a * i in
      let i_block' = block_length a * (i + 1) in
      let blocks1:bytes_blocks a = S.slice blocks 0 i_block in
      let blocks2:bytes_blocks a = S.slice blocks i_block i_block' in
      let s_blocks:bytes_blocks a = S.slice blocks 0 i_block' in
      Spec.Hash.Lemmas.update_multi_update a (s1, ev) block;
      Spec.Hash.Lemmas.update_multi_associative a (s0, ev) blocks1 blocks2;
      update_multi_add_extra a (s0, ev) (i+1) s_blocks
    in aux ()
  in
  (**) assert (B.length blocks = U32.v n_blocks * block_length a);
  (**) add_extra_i_zero a ev;
  C.Loops.for 0ul n_blocks inv f;
  add_extra_i a ev n_blocks

noextract inline_for_extraction
val mk_update_last: a:hash_alg{is_blake a} -> update_multi_st a -> update_last_st a

let mk_update_last a update_multi s ev prev_len input input_len =
  ST.push_frame ();
  let h0 = ST.get () in

  (* Get a series of complete blocks. *)
  let blocks_n = U32.(input_len /^ block_len a) in
  let blocks_len = U32.(blocks_n *^ block_len a) in
  assert (U32.v blocks_len % block_length a = 0);
  let blocks = B.sub input 0ul blocks_len in

  let ev' = update_multi s ev blocks blocks_n in

  let h1 = ST.get () in

  assert (S.equal (as_seq h1 s) (fst (Spec.Agile.Hash.update_multi a (as_seq h0 s, ev) (B.as_seq h0 blocks))));

  let rest_len = U32.(input_len -^ blocks_len) in

  calc (==) {
    v rest_len % block_length a;
    (==) { }
    ((v input_len - v blocks_len) % pow2 64) % block_length a;
    (==) {
      assert_norm (block_length Blake2S == pow2 6);
      assert_norm (block_length Blake2B == pow2 7);
      FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v input_len - v blocks_len) 6 64;
      FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v input_len - v blocks_len) 6 64
      }
    (v input_len - v blocks_len) % block_length a;
    (==) { FStar.Math.Lemmas.lemma_mod_sub_distr (v input_len) (v blocks_len) (block_length a) }
    v input_len % block_length a;
  };

  calc (==) {
    (block_length a - (len_v a prev_len + v input_len) ) % block_length a;
    (==) { FStar.Math.Lemmas.lemma_mod_sub_distr (block_length a - v input_len) (len_v a prev_len) (block_length a) }
    (block_length a - v input_len) % block_length a;
    (==) { FStar.Math.Lemmas.lemma_mod_sub_distr (block_length a) (v input_len) (block_length a) }
    (block_length a - (v input_len % block_length a)) % block_length a;
    (==) { }
    (block_length a - (v rest_len % block_length a)) % block_length a;
    (==) { FStar.Math.Lemmas.lemma_mod_sub_distr (block_length a) (v rest_len) (block_length a) }
    (block_length a - v rest_len) % block_length a;
  };

  (* The rest that doesn't make up a complete block *)
  if rest_len = 0ul then
    (assert (Spec.Hash.PadFinish.pad a (len_v a prev_len + v input_len) `Seq.equal` Seq.empty);
     assert (S.equal
      (B.as_seq h0 input `Seq.append` (Spec.Hash.PadFinish.pad a (len_v a prev_len + v input_len)))
      (B.as_seq h1 blocks));
    ST.pop_frame();
    ev'
    )
  else (
    let rest = B.sub input blocks_len rest_len in


    let pad_len = U32.(block_len a -^ rest_len) in

    let tmp = B.alloca (Lib.IntTypes.u8 0) (block_len a) in
    let tmp_rest = B.sub tmp 0ul rest_len in
    let tmp_pad = B.sub tmp rest_len pad_len in
    B.blit rest 0ul tmp_rest 0ul rest_len;

    calc (==) {
      (block_length a - (len_v a prev_len + v input_len) ) % block_length a;
      (==) { }
      (block_length a - v rest_len) % block_length a;
      (==) { FStar.Math.Lemmas.small_mod (block_length a - v rest_len) (block_length a) }
      block_length a - v rest_len;
      (==) { assert_norm (block_length a <= pow2 32); FStar.Math.Lemmas.small_mod (block_length a - v rest_len) (pow2 32) }
      v pad_len;
    };

    let h2 = ST.get() in

    calc (==) {
      B.as_seq h0 blocks `Seq.append` B.as_seq h2 tmp;
      (==) { assert (Seq.equal (B.as_seq h2 tmp) (B.as_seq h2 tmp_rest `Seq.append` B.as_seq h2 tmp_pad)) }
      B.as_seq h0 blocks `Seq.append` (B.as_seq h2 tmp_rest `Seq.append` B.as_seq h2 tmp_pad);
      (==) { Seq.append_assoc (B.as_seq h0 blocks) (B.as_seq h2 tmp_rest) (B.as_seq h2 tmp_pad) }
      (B.as_seq h0 blocks `Seq.append` B.as_seq h2 tmp_rest) `Seq.append` B.as_seq h2 tmp_pad;
      (==) { assert (S.equal (B.as_seq h0 input) (S.append (B.as_seq h0 blocks) (B.as_seq h2 tmp_rest))) }
      B.as_seq h0 input `Seq.append` B.as_seq h2 tmp_pad;
      (==) { assert (B.as_seq h2 tmp_pad `S.equal` Spec.Hash.PadFinish.pad a (len_v a prev_len + v input_len)) }
      B.as_seq h0 input `Seq.append` Spec.Hash.PadFinish.pad a (len_v a prev_len + v input_len);
    };

    let ev_f = update_multi s ev' tmp 1ul in

    let h3 = ST.get() in

    Spec.Hash.Lemmas.update_multi_associative a (as_seq h0 s, ev) (B.as_seq h0 blocks) (B.as_seq h2 tmp);

    ST.pop_frame();
    ev_f
  )
#pop-options

let update_multi_blake2s: update_multi_st Blake2S =
  mk_update_multi Blake2S update_blake2s
let update_multi_blake2b: update_multi_st Blake2B =
  mk_update_multi Blake2B update_blake2b

let update_last_blake2s: update_last_st Blake2S =
  mk_update_last Blake2S update_multi_blake2s
let update_last_blake2b: update_last_st Blake2B =
  mk_update_last Blake2B update_multi_blake2b

let lemma_blake2_hash_equivalence
  (a:hash_alg{is_blake a}) (d:bytes{Seq.length d <= max_input_length a})
  : Lemma
    (Spec.blake2 (to_blake_alg a) d 0 Seq.empty (Spec.max_output (to_blake_alg a)) ==
     Spec.Agile.Hash.hash a d)
  = admit()

let hash_blake2s: hash_st Blake2S = fun input input_len dst ->
  let h0 = ST.get() in
  Hacl.Blake2s_32.blake2s 32ul dst input_len input 0ul (B.null #uint8);
  lemma_blake2_hash_equivalence Blake2S (B.as_seq h0 input)

let hash_blake2b: hash_st Blake2B = fun input input_len dst ->
  let h0 = ST.get() in
  Hacl.Blake2b_32.blake2b 64ul dst input_len input 0ul (B.null #uint8);
  lemma_blake2_hash_equivalence Blake2B (B.as_seq h0 input)
