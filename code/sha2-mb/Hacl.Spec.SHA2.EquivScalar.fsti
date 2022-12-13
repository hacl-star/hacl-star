module Hacl.Spec.SHA2.EquivScalar

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Spec.Hash.Definitions
open Hacl.Spec.SHA2

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val update_lemma: a:sha2_alg -> block:block_t a -> hash:words_state a ->
  Lemma (update a block hash == Spec.Agile.Hash.update a hash block)

val repeat_blocks_multi_extensionality:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> inp:seq a{length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> g:(lseq a blocksize -> b -> b)
  -> init:b ->
  Lemma
  (requires
    (forall (block:lseq a blocksize) (acc:b). f block acc == g block acc))
  (ensures
    repeat_blocks_multi blocksize inp f init ==
    repeat_blocks_multi blocksize inp g init)

val update_nblocks_is_repeat_blocks_multi:
     a:sha2_alg
  -> len:len_lt_max_a_t a{len % block_length a = 0}
  -> b:seq uint8{length b = len}
  -> st0:words_state a ->
  Lemma (update_nblocks a len b st0 ==
    Lib.Sequence.repeat_blocks_multi (block_length a) b (update a) st0)

val update_nblocks_is_repeat_blocks_multi':
     a:sha2_alg
  -> len:len_lt_max_a_t a
  -> b:seq uint8{length b = len}
  -> st0:words_state a ->
  Lemma (update_nblocks a len b st0 ==
    repeat_blocks_multi (block_length a) (Seq.slice b 0 (Seq.length b - Seq.length b % block_length a)) (update a) st0)

val hash_is_repeat_blocks:
     a:sha2_alg
  -> len:len_lt_max_a_t a
  -> b:seq uint8{length b = len}
  -> st0:words_state a ->
  Lemma
   (let len' : len_t a = mk_len_t a len in
    let st = update_nblocks a len b st0 in
    let rem = len % block_length a in
    let mb = Seq.slice b (len - rem) len in
    update_last a len' rem mb st ==
    Lib.Sequence.repeat_blocks (block_length a) b (update a) (update_last a len') st0)

val hash_agile_lemma: #a:sha2_alg -> len:len_lt_max_a_t a -> b:seq uint8{length b = len} ->
  Lemma (hash #a len b == Spec.Agile.Hash.hash a b)
