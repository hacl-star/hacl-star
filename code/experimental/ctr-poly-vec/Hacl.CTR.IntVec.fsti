module Hacl.CTR.IntVec

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.Sequence.Lemmas
open Lib.ByteSequence
open Lib.IntVector


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

///
///  Cipher
///

val state_t: v_inttype
val statesize: len:size_pos{len * numbytes state_t < pow2 32}
let state = lseq (uint_t state_t SEC) statesize

val key: Type0
val nonce: Type0
let counter = size_nat

let blocksize = statesize * numbytes state_t
let block = lbytes blocksize

val init: key -> nonce -> counter -> state
val kb: state -> counter -> state


///
///  CTR
///

let xor_block (kb:state) (b:block) : block =
  let ib = uints_from_bytes_le b in
  let ob = map2 (^.) ib kb in
  uints_to_bytes_le ob

let encrypt_block (st0:state) (c:counter) (b:block) : block =
  let k = kb st0 c in
  xor_block k b

let ctr (k:key) (n:nonce) (c0:counter) (msg:bytes{length msg / blocksize <= max_size_t}) : (cipher:bytes{length cipher == length msg}) =
  let st0 = init k n c0 in
  map_blocks_ctr #uint8 blocksize msg (encrypt_block st0) (u8 0)

///
///  CipherxN
///

let width_t = w:width{w * blocksize <= max_size_t}
let blocksize_v (w:width_t) : size_pos = w * blocksize
let block_v w = lbytes (blocksize_v w)

let uintxN (w:width_t) = vec_t state_t w
let state_v (w:width_t) = lseq (uintxN w) statesize

val init_v: #w:width_t -> key -> nonce -> counter -> state_v w
val kb_v: #w:width_t -> state_v w -> counter -> state_v w


///
///  CTRxN
///

let xor_block_v_f (#w:width_t) (k:state_v w) (i:nat{i < statesize}) (b:lbytes (w * numbytes state_t)) : lbytes (w * numbytes state_t) =
  let x = vec_from_bytes_le state_t w b in
  let y = x ^| k.[i] in
  vec_to_bytes_le y

let xor_block_v (#w:width_t) (kb:state_v w) (b:block_v w) : block_v w =
  map_blocks_multi (w * numbytes state_t) statesize statesize b (xor_block_v_f #w kb)

//TODO: add generic transpose
val transpose: #w:width_t -> state_v w -> state_v w

let encrypt_block_v (#w:width_t) (st0:state_v w) (c:counter) (b:block_v w) : block_v w =
  let kb = kb_v st0 c in
  let k = transpose kb in
  xor_block_v k b

let ctr_v (#w:width_t) (k:key) (n:nonce) (c0:counter) (msg:bytes{length msg / (w * blocksize) <= max_size_t}) : (cipher:bytes{length cipher == length msg}) =
  let st_v0 = init_v k n c0 in
  map_blocks_ctr #uint8 (w * blocksize) msg (encrypt_block_v st_v0) (u8 0)


///
///  CTR properties
///

val kb_equiv_lemma: #w:width_t -> k:key -> n:nonce -> ctr0:counter -> ctr:counter{ctr0 + w - 1 <= max_size_t} -> i:nat{i < w /\ w * ctr + i <= max_size_t} ->
  Lemma (kb (init k n ctr0) (w * ctr + i) == kb (init k n (ctr0 + i)) (w * ctr))

val transpose_state_i: #w:width_t -> st_v:state_v w -> i:nat{i < w} -> state

val init_v_i: #w:width_t -> k:key -> n:nonce -> ctr0:counter{ctr0 + w - 1 <= max_size_t} -> i:nat{i < w} ->
  Lemma (transpose_state_i (init_v #w k n ctr0) i == init k n (ctr0 + i))

val kb_v_i: #w:width_t -> ctr:counter{w * ctr <= max_size_t} -> st_v0:state_v w -> i:nat{i < w} ->
  Lemma (transpose_state_i (kb_v st_v0 ctr) i == kb (transpose_state_i st_v0 i) (w * ctr))

val transpose_lemma_i: #w:width_t -> st_v:state_v w -> i:nat{i < w * statesize} ->
  Lemma (div_mul_lt w i statesize; div_mul_lt statesize i w;
    (vec_v (transpose #w st_v).[i / w]).[i % w] == (transpose_state_i st_v (i / statesize)).[i % statesize])
