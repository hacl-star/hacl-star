module Spec.HMAC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


module H = Spec.Hash


(* Key wrapping function *)
let wrap_key (a:H.algorithm) (len:size_nat{len < H.max_input a}) (key:lbytes len) =
  let block = create (H.size_block a) (u8 0) in
  if len <= H.size_block a then
    update_slice block 0 len key
  else begin
    let nkey = H.hash a key in
    update_slice block 0 (H.size_hash a) nkey
  end


let init (a:H.algorithm) (okey:lbytes (H.size_block a)) =

  (* Define ipad and opad *)
  let ipad = create (H.size_block a) (u8 0x36) in

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad okey in

  (* Step 3a: feed s2 to the inner hash function *)
  H.update_block a s2 (H.init a)


let update_block (a:H.algorithm) block chash = H.update_block a block chash

let update_last (a:H.algorithm) prev len last hash = H.update_last a prev len last hash


let finish (a:H.algorithm) (key:lbytes (H.size_block a)) (hash:H.state a) =

  (* Define opad *)
  let opad = create (H.size_block a) (u8 0x5c) in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = H.finish a hash in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = map2 (fun x y -> logxor x y) opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  let hash0 = H.update_block a s5 (H.init a) in
  let hash1 = H.update_last a (H.size_block a) (H.size_hash a) s4 hash0 in
  let hash2 = H.finish a hash1 in
  hash2


let hmac (a:H.algorithm) (klen:size_nat{klen <= H.max_input a}) (key:lbytes klen) (len:size_nat{klen + len + H.size_block a <= H.max_input a}) (input:lbytes len) =
  let okey = wrap_key a klen key in
  let hash0 = init a okey in
  let hash1 = repeati_blocks (H.size_block a) input
    (fun i -> update_block a)
    (fun i -> update_last a ((i + 1) * (H.size_block a))) hash0 in
  finish a okey hash1
