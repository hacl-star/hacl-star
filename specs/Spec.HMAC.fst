module Spec.HMAC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


module H = Spec.Hash.Definitions


(* Key wrapping function *)
let wrap_key (a:H.hash_alg) (key:bytes{length key < H.max_input_length a}) =
  let block = create (H.block_length a) (u8 0) in
  let len = length key in
  if len <= H.block_length a then
    update_slice block 0 len key
  else begin
    let nkey = Spec.Hash.hash a key in
    update_slice block 0 (H.hash_length a) nkey
  end

let init (a:H.hash_alg) (okey:lbytes (H.block_length a)) =

  (* Define ipad and opad *)
  let ipad = create (H.block_length a) (u8 0x36) in

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad okey in

  (* Step 3a: feed s2 to the inner hash function *)
  Spec.Hash.update a (Spec.Hash.init a) s2


let update_block (a:H.hash_alg) block chash = Spec.Hash.update a chash block

let update_last (a:H.hash_alg) prev len last hash =
  Spec.Hash.Incremental.update_last a hash prev last

#set-options "--max_ifuel 1 --max_fuel 0"

let small_block_hash_length (a: H.hash_alg) : Lemma (ensures (
  H.block_length a + H.hash_length a < H.max_input_length a
)) =
  let open FStar.Mul in
  assert_norm(8 * 16 + 8 * 8 < pow2 61);
  assert_norm(pow2 61 < pow2 125)

let finish (a:H.hash_alg) (key:lbytes (H.block_length a)) (hash:H.words_state a) =

  (* Define opad *)
  let opad = create (H.block_length a) (u8 0x5c) in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Spec.Hash.PadFinish.finish a hash in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = map2 (fun x y -> logxor x y) opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  small_block_hash_length a;
  Spec.Hash.hash a (concat #uint8 #(H.block_length a) #(H.hash_length a) s5 s4)

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

let hmac
  (a:H.hash_alg)
  (key:bytes{length key < H.max_input_length a})
  (input:bytes{length key + length input + H.block_length a < H.max_input_length a}) =
  let klen = length key in
  let ilen = length input in
  let okey = wrap_key a key in
  let hash0 = init a okey in
  let hash1 = repeati_blocks (H.block_length a) input
    (fun i -> update_block a)
    (fun i -> update_last a ((i + 1) * (H.block_length a))) hash0 in
  finish a okey hash1
