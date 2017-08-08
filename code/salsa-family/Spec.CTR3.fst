module Spec.CTR3

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Seq
open Spec.Lib

open Spec.CTR


#reset-options "--max_fuel 0"

val counter_mode_blocks3:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t ->
  len:nat{192 * len = length plain /\ c + 3 * len < pow2 32} ->
  Tot (lbytes (length plain))
      (decreases (len))
#reset-options "--z3rlimit 20 --max_fuel 0"
let rec counter_mode_blocks3 key nonce counter plain len =
  if len = 0 then Seq.createEmpty #UInt8.t
  else (
    assert(length plain >= 192);
    let prefix, block = split plain (length plain - 192) in
    let cipher  = counter_mode_blocks3 key nonce counter prefix (len - 1) in
    let mask0   = Spec.Chacha20_vec.chacha20_block key nonce (counter + 3 * len - 3) in
    let mask1   = Spec.Chacha20_vec.chacha20_block key nonce (counter + 3 * len - 2) in
    let mask2   = Spec.Chacha20_vec.chacha20_block key nonce (counter + 3 * len - 1) in
    let block0  = slice block 0   64  in
    let block1  = slice block 64  128 in
    let block2  = slice block 128 192 in
    let cipher0 = xor #64 block0 mask0 in
    let cipher1 = xor #64 block1 mask1 in
    let cipher2 = xor #64 block2 mask2 in
    let eb      = cipher0 @| cipher1 @| cipher2 in
    cipher @| eb
  )

val counter_mode_blocks:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t ->
  len:nat{64 * len = length plain /\ c + len < pow2 32} ->
  Tot (lbytes (length plain))
#reset-options "--z3rlimit 20 --max_fuel 0"
let counter_mode_blocks key nonce counter plain len =
  let len3 = len / 3 in
  let rest3 = len % 3 in
  let plain3, plain3' = split plain (len3 * 192) in
  let cipher3 = counter_mode_blocks3 key nonce counter plain3 len3 in
  let cipher3' =
  if rest3 = 2 then
    let mask0  = Spec.Chacha20_vec.chacha20_block key nonce (counter + 3 * len3) in
    let mask1  = Spec.Chacha20_vec.chacha20_block key nonce (counter + 3 * len3 + 1) in
    let mask   = mask0 @| mask1 in
    let block0  = slice plain3' 0   64  in
    let block1  = slice plain3' 64  128 in
    let cipher0 = xor #64 block0 mask0 in
    let cipher1 = xor #64 block1 mask1 in
    cipher0 @| cipher1
  else if rest3 = 1 then
    let mask   = Spec.Chacha20_vec.chacha20_block key nonce (counter + 3 * len3) in
    xor #64 plain3' mask
  else createEmpty in
  cipher3 @| cipher3'

val counter_mode:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t{c + length plain / 64 < pow2 32} ->
  Tot (lbytes (length plain))
#reset-options "--z3rlimit 20 --max_fuel 0"
let counter_mode key nonce counter plain =
  let len = length plain in
  let len64      = len / 64 in
  let blocks_len = 64 * (len / 64) in
  let part_len   = len % 64 in
  let blocks, last_block = split plain blocks_len in
  let cipher_blocks = counter_mode_blocks key nonce counter blocks len64 in
  let cipher_last_block =
    if part_len > 0
    then (* encrypt final partial block(s) *)
      let mask = Spec.Chacha20_vec.chacha20_block key nonce (counter+len64) in
      let mask = slice mask 0 part_len in
      assert(length last_block = part_len);
      xor #part_len last_block mask
    else createEmpty in
  cipher_blocks @| cipher_last_block


val lemma_counter_mode_blocks_def1:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t ->
  len:nat{64 * len = length plain /\ c + len < pow2 32 /\ length plain >= 64} ->
  Lemma (Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx
                                      Spec.Chacha20_vec.chacha20_cipher k n c plain ==
                  (let len  = length plain in
                   let len' = len / 64 in
                   let prefix, block = split plain (len - 64) in
                   Math.Lemmas.lemma_mod_plus (length prefix) 1 (64);
                   Math.Lemmas.lemma_div_le (length prefix) len 64;
                   Spec.CTR.Lemmas.lemma_div len (64);
                   let cipher = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx
                                                             Spec.Chacha20_vec.chacha20_cipher
                                                             k n c prefix in
                   let mask   = Spec.Chacha20_vec.chacha20_block k n (c+(len/64-1)) in
                   let eb     = xor block mask in
                   cipher @| eb))
#reset-options "--z3rlimit 200 --max_fuel 1"
let lemma_counter_mode_blocks_def1 k n c plain len =
  assert(len > 0)


#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_counter_mode_blocks_def0:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t{length plain = 0} ->
  Lemma (Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx
                                      Spec.Chacha20_vec.chacha20_cipher k n c plain ==
         createEmpty)
#reset-options "--z3rlimit 200 --max_fuel 1"
let lemma_counter_mode_blocks_def0 k n c plain = ()

#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_counter_mode_blocks3_def1:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t ->
  len:nat{192 * len = length plain /\ c + 3 * len < pow2 32 /\ len > 0} ->
  Lemma (counter_mode_blocks3 k n c plain len ==
    (let prefix, block = split plain (length plain - 192) in
     let cipher  = counter_mode_blocks3 k n c prefix (len - 1) in
     let mask0   = Spec.Chacha20_vec.chacha20_block k n (c + 3 * len - 3) in
     let mask1   = Spec.Chacha20_vec.chacha20_block k n (c + 3 * len - 2) in
     let mask2   = Spec.Chacha20_vec.chacha20_block k n (c + 3 * len - 1) in
     let block0  = slice block 0   64  in
     let block1  = slice block 64  128 in
     let block2  = slice block 128 192 in
     let cipher0 = xor #64 block0 mask0 in
     let cipher1 = xor #64 block1 mask1 in
     let cipher2 = xor #64 block2 mask2 in
     let eb      = cipher0 @| cipher1 @| cipher2 in
     cipher @| eb))
#reset-options "--z3rlimit 200 --max_fuel 1"
let lemma_counter_mode_blocks3_def1 k n c plain len = ()

#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_counter_mode_blocks3_def0:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t{length plain = 0} ->
  Lemma (counter_mode_blocks3 k n c plain 0 == createEmpty)
#reset-options "--z3rlimit 200 --max_fuel 1"
let lemma_counter_mode_blocks3_def0 k n c plain = ()

#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_counter_mode_blocks3_eq:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t ->
  len:nat{192 * len = length plain /\ c + 3 * len < pow2 32} ->
  Lemma (requires (True))
        (ensures (Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_cipher k n c plain == counter_mode_blocks3 k n c plain len))
        (decreases len)

#reset-options "--z3rlimit 200 --max_fuel 0"

let rec lemma_counter_mode_blocks3_eq k n c plain len =
  if len = 0 then (
    lemma_counter_mode_blocks3_def0 k n c plain;
    lemma_counter_mode_blocks_def0 k n c plain)
  else (
    let mask0   = Spec.Chacha20_vec.chacha20_block k n (c + 3 * len - 3) in
    let mask1   = Spec.Chacha20_vec.chacha20_block k n (c + 3 * len - 2) in
    let mask2   = Spec.Chacha20_vec.chacha20_block k n (c + 3 * len - 1) in
    let prefix, blocks = split plain (length plain - 192) in
    let block0 = slice blocks 0   64 in
    let block1 = slice blocks 64  128 in
    let block2 = slice blocks 128 192 in
    let cipher0 = xor #64 block0 mask0 in
    let cipher1 = xor #64 block1 mask1 in
    let cipher2 = xor #64 block2 mask2 in
    lemma_counter_mode_blocks3_eq k n c prefix (len - 1);
    let cipher = counter_mode_blocks3 k n c plain len in
    lemma_eq_intro plain (((prefix @| block0) @| block1) @| block2);
    lemma_counter_mode_blocks_def1 k n c (((prefix @| block0) @| block1) @| block2) (3 * len);
    lemma_counter_mode_blocks_def1 k n c ((prefix @| block0) @| block1) (3 * len - 1);
    lemma_counter_mode_blocks_def1 k n c (prefix @| block0) (3 * len - 2);
    let x = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_block k n c plain in
    let y = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_block k n c ((prefix @| block0) @| block1) in
    let z = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_block k n c ((prefix @| block0)) in
    let w = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_block k n c prefix in
    let pre, block = split plain ((3 * len) * 64 - 64) in
    lemma_eq_intro block (slice blocks 128 192);
    lemma_eq_intro pre ((prefix @| block0) @| block1);
    Math.Lemmas.lemma_mod_plus (length pre) 1 (64);
    Math.Lemmas.lemma_div_le (length pre) (length plain) 64;
    Spec.CTR.Lemmas.lemma_div (length plain) (64);
    assert(c + (length plain / 64 - 1) = c + 3 * len - 1);
    assert(c + ((length plain - 64) / 64 - 1) = c + 3 * len - 2);
    assert(c + ((length plain - 128) / 64 - 1) = c + 3 * len - 3);
    let mask' = Spec.Chacha20_vec.chacha20_block k n (c + (length plain / 64) - 1) in
    let cip   = xor #64 block mask' in
    lemma_eq_intro cip cipher2;
    lemma_eq_intro (y @| cipher2) x;
    let pre, block = split ((prefix @| block0)  @| block1) ((3 * len - 1) * 64 - 64) in
    lemma_eq_intro block block1;
    lemma_eq_intro pre ((prefix @| block0));
    lemma_eq_intro (z @| cipher1) y;
    let pre, block = split ((prefix @| block0)) ((3 * len - 2) * 64 - 64) in
    lemma_eq_intro block block0;
    lemma_eq_intro pre ((prefix));
    lemma_eq_intro (w @| cipher0) z;
    lemma_counter_mode_blocks3_def1 k n c plain len;
    lemma_eq_intro (slice (((prefix @| block0) @| block1) @| block2) (length plain - 64) (length plain)) block2;
    lemma_eq_intro (slice (((prefix @| block0) @| block1)) (length plain - 128) (length plain - 64)) block1;
    lemma_eq_intro (slice (((prefix @| block0))) (length plain - 192) (length plain - 128)) block0;
    let cipher'' = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_block k n c prefix in
    let cipher' = cipher0 @| cipher1 @| cipher2 in
    lemma_eq_intro cipher' (slice cipher (length plain - 192) (length plain));
    lemma_eq_intro cipher'' (slice cipher 0 (length prefix));
    lemma_eq_intro (cipher') (cipher0 @| cipher1 @| cipher2);
    lemma_eq_intro (cipher @| (cipher0 @| cipher1 @| cipher2)) (((cipher @| cipher0) @| cipher1) @| cipher2);
    lemma_eq_intro x (y @| cipher2);
    lemma_eq_intro x (w @| (cipher0 @| cipher1 @| cipher2));
    lemma_eq_intro (Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_cipher k n c plain) (counter_mode_blocks3 k n c plain len)
  )


val lemma_counter_mode_blocks_eq:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t ->
  len:nat{64 * len = length plain /\ c + len < pow2 32} ->
  Lemma (Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_cipher k n c plain == counter_mode_blocks k n c plain len)

#reset-options "--z3rlimit 200 --max_fuel 0"

let lemma_counter_mode_blocks_eq k n c plain len =
  let len3 = len / 3 in
  let rest3 = len % 3 in
  let plain3, plain3' = split plain (len3 * 192) in
  lemma_counter_mode_blocks3_eq k n c plain3 len3;
  let cipher3 = counter_mode_blocks3 k n c plain3 len3 in
  if rest3 = 2 then (
    assert(c + ((length plain - 64) / 64 - 3) = c + 3 * len3 - 2);
    let mask0   = Spec.Chacha20_vec.chacha20_block k n (c + length plain / 64 - 2) in
    let mask1   = Spec.Chacha20_vec.chacha20_block k n (c + length plain / 64 - 1) in
    let prefix, blocks = split plain (length plain - 128) in
    let block0 = slice blocks 0   64 in
    let block1 = slice blocks 64  128 in
    let cipher0 = xor #64 block0 mask0 in
    let cipher1 = xor #64 block1 mask1 in
    lemma_eq_intro plain (((prefix @| block0) @| block1));
    lemma_counter_mode_blocks_def1 k n c ((prefix @| block0) @| block1) (length plain / 64);
    lemma_counter_mode_blocks_def1 k n c (prefix @| block0) (length plain / 64 - 1);
    let x = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_block k n c plain in
    let y = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_block k n c ((prefix @| block0)) in
    let z = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_block k n c prefix in
    let pre, block = split plain (length plain - 64) in
    lemma_eq_intro block (slice blocks 64 128);
    lemma_eq_intro pre ((prefix @| block0));
    Math.Lemmas.lemma_mod_plus (length pre) 1 (64);
    Math.Lemmas.lemma_div_le (length pre) (length plain) 64;
    Spec.CTR.Lemmas.lemma_div (length plain) (64);
    let mask' = Spec.Chacha20_vec.chacha20_block k n (c + (length plain / 64) - 1) in
    let cip   = xor #64 block mask' in
    lemma_eq_intro cip cipher1;
    lemma_eq_intro (y @| cipher1) x;
    let pre, block = split (prefix @| block0) (length plain - 128) in
    lemma_eq_intro block block0;
    lemma_eq_intro pre prefix;
    lemma_eq_intro pre plain3;
    lemma_eq_intro (z @| cipher0) y;
    lemma_eq_intro x (z @| (cipher0 @| cipher1));
    lemma_eq_intro (Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_cipher k n c plain) (counter_mode_blocks k n c plain len)
  )
  else if rest3 = 1 then (
    lemma_counter_mode_blocks_def1 k n c plain (length plain / 64);
    lemma_eq_intro (Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_cipher k n c plain) (counter_mode_blocks k n c plain len)
  ) else (
    assert(rest3 = 0);
    let x = Spec.CTR.counter_mode_blocks Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_cipher k n c plain in
    let x' = counter_mode_blocks k n c plain len in
    lemma_eq_intro cipher3 (cipher3 @| createEmpty);
    lemma_eq_intro cipher3 (cipher3 @| createEmpty);
    lemma_eq_intro plain plain3)



val lemma_counter_mode3_eq:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t{c + length plain / 64 < pow2 32} ->
  Lemma (Spec.CTR.counter_mode Spec.Chacha20_vec.chacha20_ctx Spec.Chacha20_vec.chacha20_cipher k n c plain == counter_mode k n c plain)
let lemma_counter_mode3_eq k n c plain =
  let len = length plain / 64 in
  let plain, _ = split plain (64 * len) in
  lemma_counter_mode_blocks_eq k n c plain len
