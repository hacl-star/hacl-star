module Hacl.CTR

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.Sequence.Lemmas
open Lib.ByteSequence


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

///
///  Cipher
///

val blocksize : size_pos
let block = lbytes blocksize

val state: Type0
val key: Type0
val nonce: Type0
let counter = size_nat

val init: key -> nonce -> counter -> state
val kb: state -> counter -> block


///
///  CTR
///

let encrypt_block (st0:state) (c:counter) (b:block) : block =
  let kb = kb st0 c in
  map2 (^.) kb b

let encrypt_last (st0:state) (c:counter) (len:nat{len < blocksize}) (r:lbytes len) : lbytes len =
  let b = create blocksize (u8 0) in
  let b = update_sub b 0 len r in
  let cipher = encrypt_block st0 c b in
  sub cipher 0 len

let ctr (k:key) (n:nonce) (c0:counter) (msg:bytes{length msg / blocksize <= max_size_t}) : (cipher:bytes{length cipher == length msg}) =
  let st0 = init k n c0 in
  map_blocks #uint8 blocksize msg (encrypt_block st0) (encrypt_last st0)

///
///  CipherxN
///

let width_t = w:size_pos{w * blocksize <= max_size_t}
let blocksize_v (w:width_t) : size_pos = w * blocksize
let block_v w = lbytes (blocksize_v w)

val state_v: w:width_t -> Type0

val init_v: #w:width_t -> key -> nonce -> counter -> state_v w
val kb_v: #w:width_t -> state_v w -> counter -> block_v w


///
///  CTRxN
///

let encrypt_block_v (#w:width_t) (st0:state_v w) (c:counter) (b:block_v w) : block_v w =
  let kb = kb_v st0 c in
  map2 (^.) kb b

let encrypt_last_v (#w:width_t) (st0:state_v w) (c:counter) (len:nat{len < blocksize_v w}) (r:lbytes len) : lbytes len =
  let b = create (w * blocksize) (u8 0) in
  let b = update_sub b 0 len r in
  let cipher = encrypt_block_v st0 c b in
  sub cipher 0 len

let ctr_v (#w:width_t) (k:key) (n:nonce) (c0:counter) (msg:bytes{length msg / (w * blocksize) <= max_size_t}) : (cipher:bytes{length cipher == length msg}) =
  let st_v0 = init_v k n c0 in
  map_blocks #uint8 (w * blocksize) msg (encrypt_block_v st_v0) (encrypt_last_v st_v0)


///
///  CTR properties
///

val kb_equiv_lemma: #w:width_t -> k:key -> n:nonce -> ctr0:counter -> ctr:counter{ctr0 + w - 1 <= max_size_t} -> i:nat{i < w /\ w * ctr + i <= max_size_t} ->
  Lemma (kb (init k n ctr0) (w * ctr + i) == kb (init k n (ctr0 + i)) (w * ctr))

val transpose_state_i: #w:width_t -> st_v:state_v w -> i:nat{i < w} -> state

val init_v_i: #w:width_t -> k:key -> n:nonce -> ctr0:counter{ctr0 + w - 1 <= max_size_t} -> i:nat{i < w} ->
  Lemma (transpose_state_i (init_v #w k n ctr0) i == init k n (ctr0 + i))

val kb_v_i: #w:width_t -> ctr:counter{w * ctr <= max_size_t} -> st_v0:state_v w -> i:nat{i < w} -> Lemma
  (assert ((i + 1) * blocksize <= w * blocksize);
   sub (kb_v st_v0 ctr) (i * blocksize) blocksize == kb (transpose_state_i st_v0 i) (w * ctr))
