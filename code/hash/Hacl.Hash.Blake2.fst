module Hacl.Hash.Blake2

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

open Lib.IntTypes

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

open Hacl.Hash.Lemmas
open Spec.Blake2.Lemmas

open FStar.Mul

#set-options "--fuel 0 --ifuel 0"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"

(*** update_multi *)
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

(*** update_last *)

noextract inline_for_extraction
val split (a : hash_alg{is_blake a}) (input_len : size_t) :
  Pure (size_t & size_t & size_t)
  (requires True)
  (ensures fun (blocks_n, blocks_len, rest_len) ->
    U32.v blocks_len == U32.v blocks_n * block_length a /\
    (U32.v blocks_n, U32.v rest_len) == Spec.Blake2.split (to_blake_alg a) (U32.v input_len))

let split a input_len =
  let blocks_n = U32.(input_len /^ block_len a) in
  let blocks_len = U32.(blocks_n *^ block_len a) in
  let rest_len = U32.(input_len -^ blocks_len) in
  if U32.(rest_len =^ 0ul) && U32.(blocks_n >^ 0ul) then
    begin
    let blocks_n = U32.(blocks_n -^ 1ul) in
    let blocks_len = U32.(blocks_len -^ block_len a) in
    let rest_len = block_len a in
    blocks_n, blocks_len, rest_len
    end
  else blocks_n, blocks_len, rest_len


(* The stateful signature for [Spec.Blake2.blake2_update_last], but where
 * the input is actually the remaining data (smaller than a block) *)
noextract inline_for_extraction
let blake2_update_last_block_st (a : hash_alg{is_blake a}) =
  s:state a ->
  ev:extra_state a ->
  input:B.buffer uint8 ->
  input_len:size_t { B.length input == v input_len /\ v input_len <= block_length a /\
                     (v #U64 #SEC ev) + v input_len <= max_input a } ->
  ST.Stack (extra_state a)
    (requires (fun h ->
      B.live h s /\ B.live h input /\ B.disjoint s input))
    (ensures (fun h0 ev' h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      as_seq h1 s ==
        Spec.Blake2.blake2_update_last (to_blake_alg a) (v #U64 #SEC ev)
                                       (v input_len) (B.as_seq h0 input) (as_seq h0 s)))

noextract inline_for_extraction
val mk_update_last: a:hash_alg{is_blake a} -> update_multi_st a ->
                    blake2_update_last_block_st a -> update_last_st a

let mk_update_last a update_multi blake2_update_last_block s ev prev_len input input_len =
  ST.push_frame ();
  (**) let h0 = ST.get () in
  (**) let input_v : Ghost.erased _ = B.as_seq h0 input in
  (* Compute the lengths to split the blocks *)
  let blocks_n, blocks_len, rest_len = split a input_len in
  (* Call update_multi on the longest series of complete blocks *)
  (**) assert (U32.v blocks_len % block_length a = 0);
  let blocks = B.sub input 0ul blocks_len in
  (**) let blocks_v : Ghost.erased _ = B.as_seq h0 blocks in
  (**) assert(
         let blocks_s, _, rem_s = Spec.Hash.Incremental.last_split_blake a input_v in
         blocks_v `Seq.equal` blocks_s /\ v rest_len == rem_s);
  let ev' = update_multi s ev blocks blocks_n in
  assume(v #U64 #SEC ev' == v #U64 #SEC ev + v blocks_len);
  assume(v #U64 #SEC ev == len_v a prev_len);
  let h1 = ST.get () in
  (**) assert (S.equal (as_seq h1 s)
               (fst (Spec.Agile.Hash.update_multi a (as_seq h0 s, ev) (B.as_seq h0 blocks))));
  (* Call update_block on the last padded block *)
  let rest = B.sub input blocks_len rest_len in
  (**) let rest_v : Ghost.erased _ = B.as_seq h0 rest in
  let ev_f = blake2_update_last_block s ev' rest rest_len in
  (**) let h2 = ST.get () in
  (**) assert(rest_v `Seq.equal` Seq.slice input_v (v blocks_len) (v input_len));
  (**) assert(as_seq h2 s  `Seq.equal`
         fst (Spec.Hash.Incremental.update_last_blake a (as_seq h0 s, ev)
         (len_v a prev_len) input_v));
  ST.pop_frame ();
  u64 0
#pop-options

(*
U128.uint64_to_uint128
(*
  u64 0

  admit()


let test (a:hash_alg{is_blake a})
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= max_input_length a}): unit =
  let h1 = Spec.Hash.Incremental.update_last_blake a hash prevlen input in
  (**)
  let blocks, last_block, rem = Spec.Hash.Incremental.last_split_blake a input in
  let h' = Spec.Agile.Hash.update_multi a hash blocks in
  let h_f = Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (snd h' +. u64 rem)) last_block (fst h') in
  (**)
  assume(v #U64 #SEC (snd h') == Seq.length blocks);
  assert(Seq.length input = Seq.length blocks + rem);
  let input_rem = Seq.slice input (Seq.length blocks) (Seq.length input) in
  let h2 = Spec.Blake2.blake2_update_last (to_blake_alg a) (Seq.length blocks) rem input_rem (fst h') in
  assert(h_f == h2)

  

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
  assume(rest_len <> 0ul);
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
    
  assume(B.as_seq h2 tmp `S.equal`
    Spec.Blake2.get_last_padded_block (to_blake_alg a) (B.as_seq h0 input) (U32.v rest_len));

  let ev_f = update_multi s ev' tmp 1ul in

  Spec.Hash.Lemmas.update_multi_update a (as_seq h2 s, ev') (B.as_seq h2 tmp);

  let h3 = ST.get() in

//  assume(as_seq h3 s ==
//    Spec.Agile.Hash.update_multi a (U32.v input_len)
//                                 (B.as_seq h2 tmp) (as_seq h2 s));

//  assert(as_seq h3 s ==
//    Spec.Blake2.blake2_update_block (to_blake_alg a) true (Lib.IntTypes.v #U64 #SEC ev')
//                                    (B.as_seq h2 tmp) (as_seq h2 s));
  admit()

extra_state

  Spec.Hash.Lemmas.update_multi_associative a (as_seq h0 s, ev) (B.as_seq h0 blocks)
                                            (B.as_seq h2 tmp);

  ST.pop_frame();
  ev_f
  
(****)

  assume(rest_len == 0ul);
  assert (Spec.Hash.PadFinish.pad a (len_v a prev_len + v input_len) `Seq.equal` Seq.empty);
  assert (S.equal
   (B.as_seq h0 input `Seq.append` (Spec.Hash.PadFinish.pad a (len_v a prev_len + v input_len)))
   (B.as_seq h1 blocks));
  ST.pop_frame();
  ev'


  assume(rest_len <> 0ul);
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

  Spec.Hash.Lemmas.update_multi_associative a (as_seq h0 s, ev) (B.as_seq h0 blocks)
                                            (B.as_seq h2 tmp);

  ST.pop_frame();
  ev_f

  assume(rest_len == 0ul);
  assert (Spec.Hash.PadFinish.pad a (len_v a prev_len + v input_len) `Seq.equal` Seq.empty);
  assert (S.equal
   (B.as_seq h0 input `Seq.append` (Spec.Hash.PadFinish.pad a (len_v a prev_len + v input_len)))
   (B.as_seq h1 blocks));
  ST.pop_frame();
  ev'

(******)
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

    Spec.Hash.Lemmas.update_multi_associative a (as_seq h0 s, ev) (B.as_seq h0 blocks)
                                              (B.as_seq h2 tmp);

    ST.pop_frame();
    ev_f
  )
#pop-options


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
    admit();
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
    admit();
    ev_f
  );
  admit()
#pop-options
*)

let update_multi_blake2s: update_multi_st Blake2S =
  mk_update_multi Blake2S update_blake2s
let update_multi_blake2b: update_multi_st Blake2B =
  mk_update_multi Blake2B update_blake2b

let update_last_blake2s: update_last_st Blake2S =
  mk_update_last Blake2S update_multi_blake2s
let update_last_blake2b: update_last_st Blake2B =
  mk_update_last Blake2B update_multi_blake2b

let hash_blake2s: hash_st Blake2S = fun input input_len dst ->
  let h0 = ST.get() in
  Hacl.Blake2s_32.blake2s 32ul dst input_len input 0ul (B.null #uint8);
  lemma_blake2_hash_equivalence Blake2S (B.as_seq h0 input)

let hash_blake2b: hash_st Blake2B = fun input input_len dst ->
  let h0 = ST.get() in
  Hacl.Blake2b_32.blake2b 64ul dst input_len input 0ul (B.null #uint8);
  lemma_blake2_hash_equivalence Blake2B (B.as_seq h0 input)
