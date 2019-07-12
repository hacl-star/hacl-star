module Spec.HMAC_Generic

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


module H = Spec.Hash_Generic


(* Key wrapping function *)
let wrap_key (a:H.algorithm) (key:bytes{length key <= H.max_input a}) (hlen:nat{H.range_output a hlen}) =
  let block = create (H.size_block a) (u8 0) in
  let len = length key in
  if len <= H.size_block a then
    update_slice block 0 len key
  else begin
    let nkey = H.hash a key hlen in
    update_sub block 0 hlen nkey
  end


let init (a:H.algorithm) (okey:lbytes (H.size_block a)) (hlen:nat{H.range_output a hlen}) =

  (* Define ipad and opad *)
  let ipad = create (H.size_block a) (u8 0x36) in

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad okey in

  (* Step 3a: feed s2 to the inner hash function *)
  H.update_block a 0 s2 (H.init a hlen)


let update_block (a:H.algorithm) prev block chash = H.update_block a prev block chash

let update_last (a:H.algorithm) prev last hash =
  (* BB: Remove the argument from Spec.Hash_ *)
  let len = length last in
  H.update_last a prev len last hash


let finish (a:H.algorithm) (key:lbytes (H.size_block a)) (hash:H.state a) (hlen:nat{H.range_output a hlen}) =

  (* Define opad *)
  let opad = create (H.size_block a) (u8 0x5c) in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = H.finish a hash hlen in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = map2 (fun x y -> logxor x y) opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  let hash0 = H.update_block a 0 s5 (H.init a hlen) in
  let hash1 = H.update_last a (H.size_block a) hlen s4 hash0 in
  let hash2 = H.finish a hash1 hlen in
  hash2


let hmac
  (a:H.algorithm)
  (key: bytes{length key <= H.max_input a})
  (input: bytes{length key + length input + H.size_block a <= H.max_input a})
  (hlen: nat{H.range_output a hlen}) =

  let klen = length key in
  let ilen = length input in
  let okey = wrap_key a key hlen in
  let hash0 = init a okey hlen in
  let hash1 = repeati_blocks (H.size_block a) input
    (fun i -> update_block a ((i + 1) * H.size_block a))
    (fun i _ -> update_last a ((i + 1) * H.size_block a)) hash0 in
  finish a okey hash1 hlen
