module Spec.SHA3.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

friend Spec.Agile.Hash

open FStar.Mul
module Loops = Lib.LoopCombinators
module UpdateMulti = Lib.UpdateMulti

open Lib.IntTypes

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let update_is_update_multi (a:sha3_alg) (inp:bytes{S.length inp == block_length a}) (s:words_state a)
  : Lemma (Spec.SHA3.absorb_inner (1088/8) inp s == update_multi a s () inp)
  = let rateInBytes = 1088/8 in
    let f = Spec.SHA3.absorb_inner rateInBytes in
    let bs = block_length a in
    let f' = Lib.Sequence.repeat_blocks_f bs inp f 1 in
    assert (bs == rateInBytes);
    calc (==) {
      update_multi a s () inp;
      (==) { }
      Lib.Sequence.repeat_blocks_multi #_ #(words_state a) rateInBytes inp f s;
      (==) { Lib.Sequence.lemma_repeat_blocks_multi #_ #(words_state a) bs inp f s }
      (let len = S.length inp in
       let nb = len / bs in
      Loops.repeati #(words_state a) nb (Lib.Sequence.repeat_blocks_f bs inp f nb) s);
      (==) {
        Loops.unfold_repeati 1 f' s 0;
        Loops.eq_repeati0 1 f' s }
      f' 0 s;
      (==) { assert (Seq.slice inp (0 * bs) (0 * bs + bs) `S.equal` inp) }
      f inp s;
    }

let sha3_is_incremental1
  (a: sha3_alg)
  (input: bytes): Lemma (hash_incremental a input `S.equal` (
    let s = Lib.Sequence.create 25 (u64 0) in
    let rateInBytes = 1088 / 8 in
    let delimitedSuffix = byte 0x06 in
    let bs, l = UpdateMulti.split_at_last rateInBytes input in
    let s = update_multi a s () bs in
    let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
    finish a s))
= calc (==) {
       hash_incremental a input;
       (==) { }
       (let s = init a in
        let bs, l = split_blocks a input in
        let s = update_multi a s () bs in
        let s = update_last a s (S.length bs) l in
        finish a s);
       (==) { }
       (let s = Lib.Sequence.create 25 (u64 0) in
        let rateInBytes = 1088/8 in
        let bs, l = UpdateMulti.split_at_last_lazy rateInBytes input in
        let s = update_multi a s () bs in
        let s = update_last a s (S.length bs) l in
        finish a s);
       (==) { } (
       let s = Lib.Sequence.create 25 (u64 0) in
       let rateInBytes = 1088 / 8 in
       let delimitedSuffix = byte 0x06 in
       let bs, l = UpdateMulti.split_at_last_lazy rateInBytes input in
       if S.length l = rateInBytes then
         let s = update_multi a s () bs in
         let s = Spec.SHA3.absorb_inner rateInBytes l s in
         let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes 0 S.empty s in
         finish a s
       else
         let s = update_multi a s () bs in
         let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
       finish a s
       );
       (==) { (
         let s = Lib.Sequence.create 25 (u64 0) in
         let rateInBytes = 1088 / 8 in
         let delimitedSuffix = byte 0x06 in
         let bs, l = UpdateMulti.split_at_last_lazy rateInBytes input in
         if S.length l = rateInBytes then
           let s = update_multi a s () bs in
           update_is_update_multi a l s
         else ()
         ) } (
       let s = Lib.Sequence.create 25 (u64 0) in
       let rateInBytes = 1088 / 8 in
       let delimitedSuffix = byte 0x06 in
       let bs, l = UpdateMulti.split_at_last_lazy rateInBytes input in
       if S.length l = rateInBytes then
         let s = update_multi a s () bs in
         let s = update_multi a s () l in
         let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes 0 S.empty s in
         finish a s
       else
         let s = update_multi a s () bs in
         let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
       finish a s
       );
       (==) { (
         let s = Lib.Sequence.create 25 (u64 0) in
         let rateInBytes = 1088 / 8 in
         let delimitedSuffix = byte 0x06 in
         let bs, l = UpdateMulti.split_at_last_lazy rateInBytes input in
         if S.length l = rateInBytes then
           Lib.Sequence.Lemmas.repeat_blocks_multi_split (block_length a) (S.length bs) (bs `S.append` l) (Spec.SHA3.absorb_inner rateInBytes) s
         else () ) } (
       let s = Lib.Sequence.create 25 (u64 0) in
       let rateInBytes = 1088 / 8 in
       let delimitedSuffix = byte 0x06 in
       let bs, l = UpdateMulti.split_at_last_lazy rateInBytes input in
       if S.length l = rateInBytes then
         let s = update_multi a s () (bs `S.append` l) in
         let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes 0 S.empty s in
         finish a s
       else
         let s = update_multi a s () bs in
         let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
       finish a s
       );
  };
  calc (S.equal) {
    (
       let s = Lib.Sequence.create 25 (u64 0) in
       let rateInBytes = 1088 / 8 in
       let delimitedSuffix = byte 0x06 in
       let bs, l = UpdateMulti.split_at_last_lazy rateInBytes input in
       if S.length l = rateInBytes then
         let s = update_multi a s () (bs `S.append` l) in
         let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes 0 S.empty s in
         finish a s
       else
         let s = update_multi a s () bs in
         let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
       finish a s
       );

       (S.equal) {
       let s = Lib.Sequence.create 25 (u64 0) in
       let rateInBytes = 1088 / 8 in
       let bs, l = UpdateMulti.split_at_last_lazy rateInBytes input in
       let s = update_multi a s () bs in
       if S.length l = rateInBytes then begin
         let bs', l' = UpdateMulti.split_at_last rateInBytes input in
         // TODO: strengthen this... NL arith!
         assert (bs' `S.equal` (bs `S.append` l));
         assert (l' `S.equal` S.empty)
       end else
         ()
     } (
       let s = Lib.Sequence.create 25 (u64 0) in
       // Also the block size
       let rateInBytes = 1088 / 8 in
       let delimitedSuffix = byte 0x06 in
       let bs, l = UpdateMulti.split_at_last rateInBytes input in
       let s = update_multi a s () bs in
       let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
       finish a s
     );
  }

let sha3_is_incremental2
  (a: sha3_alg)
  (input: bytes): Lemma (hash a input `S.equal` (
    let s = Lib.Sequence.create 25 (u64 0) in
    let rateInBytes = 1088 / 8 in
    let delimitedSuffix = byte 0x06 in
    let bs, l = UpdateMulti.split_at_last rateInBytes input in
    let s = update_multi a s () bs in
    let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
    finish a s))
= let rateInBytes = 1088 / 8 in
  let delimitedSuffix = byte 0x06 in
  let nb = S.length input / block_length a in
  let s = Lib.Sequence.create 25 (u64 0) in
  let bs, l = UpdateMulti.split_at_last rateInBytes input in
  assert (S.length bs / block_length a == nb);
  let f = Spec.SHA3.absorb_inner rateInBytes in
  calc (==) {
    hash a input;
    (==) { } (
      let s = Spec.SHA3.absorb s rateInBytes (S.length input) input delimitedSuffix in
      Spec.SHA3.squeeze s rateInBytes 32
      );
   (==) { Lib.Sequence.lemma_repeat_blocks (block_length a) input f (Spec.SHA3.absorb_last delimitedSuffix rateInBytes) s } (
      let s = Loops.repeati #(words_state a) nb (Lib.Sequence.repeat_blocks_f (block_length a) input f nb) s in
      let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
      Spec.SHA3.squeeze s rateInBytes 32);
   (==) {
     Lib.Sequence.Lemmas.repeati_extensionality #(words_state a) nb
       (Lib.Sequence.repeat_blocks_f (block_length a) input f nb)
       (Lib.Sequence.repeat_blocks_f (block_length a) bs f nb)
       s
     } (
      let s = Loops.repeati #(words_state a) nb (Lib.Sequence.repeat_blocks_f (block_length a) bs f nb) s in
      let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
      Spec.SHA3.squeeze s rateInBytes 32);
   (==) { Lib.Sequence.lemma_repeat_blocks_multi #_ #(words_state a) (block_length a) bs f s } (
      let s = Lib.Sequence.repeat_blocks_multi #_ #(words_state a) (block_length a) bs f s in
      let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
      Spec.SHA3.squeeze s rateInBytes 32);
    }

let sha3_is_incremental
  (a: sha3_alg)
  (input: bytes): Lemma (hash_incremental a input `S.equal` hash a input)
=
  assert (hash a input == Spec.SHA3.keccak 1088 512 (S.length input) input (byte 0x06) 32);
  calc (S.equal) {
    hash_incremental a input;
  (S.equal) { sha3_is_incremental1 a input } (
    let s = Lib.Sequence.create 25 (u64 0) in
    let rateInBytes = 1088 / 8 in
    let delimitedSuffix = byte 0x06 in
    let bs, l = UpdateMulti.split_at_last rateInBytes input in
    let s = update_multi a s () bs in
    let s = Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length l) l s in
    finish a s);
  (S.equal) { sha3_is_incremental2 a input }
    hash a input;
  }
