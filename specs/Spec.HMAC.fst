module Spec.HMAC

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

open Spec.SHA2

#set-options "--z3rlimit 25"

module Hash = Spec.SHA2


(* Key wrapping function *)
let wrap_key (p:Hash.parameters) (len:size_t{len < Hash.maxInput p}) (key:lbytes len) =
  let block = create (Hash.size_block p) (u8 0) in
  if len <= Hash.size_block p then
    update_slice block 0 len key
  else begin
    let nkey = Hash.hash p len key in
    update_slice block 0 p.size_hash nkey
  end


let init (p:Hash.parameters) (len:size_t{len < Hash.maxInput p}) (key:lbytes len) =

  (* Define ipad and opad *)
  let ipad = create (Hash.size_block p) (u8 0x36) in

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key p len key in

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad okey in

  (* Step 3a: feed s2 to the inner hash function *)
  let hash_w0 = Hash.update_block p s2 p.h0 in
  hash,okey


let init' (p:Hash.parameters) (key:lbytes (size_block p)) =

  (* Define ipad and opad *)
  let ipad = create (Hash.size_block p) (u8 0x36) in

  (* Step 1: key already has the proper length *)
  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad key in

  (* Step 3a: feed s2 to the inner hash function *)
  let hash_w0 = Hash.update_block p s2 p.h0 in
  hash_w0,key


let update_block (p:Hash.parameters) (data:lbytes (size_block p)) (hash:hash_w p) =
  Hash.update_block p data hash


let update_multi (p:Hash.parameters) (n:size_t{n * size_block p <= max_size_t}) (data:lbytes (n * size_block p)) (hash:hash_w p) =
  Hash.update_multi p n data hash


let update_last (p:Hash.parameters) (n:size_t) (len:size_t{len < size_block p /\ len + n * size_block p <= maxInput p}) (last:lbytes len) (hash:hash_w p) =
  Hash.update_last p n len last hash


let finish (p:Hash.parameters) (key:lbytes (size_block p)) (hash:hash_w p) =

  (* Define opad *)
  let opad = create (Hash.size_block p) (u8 0x5c) in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Hash.finish p hash in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = map2 (fun x y -> logxor x y) opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  let hash0 = Hash.update_block p s5 p.h0 in
  let hash1 = Hash.update_last p 1 (p.size_hash) s4 hash0 in
  let hash2 = Hash.finish p hash1 in
  hash2


(* Core HMAC function for a key of length size_block *)
let hmac_core' (p:Hash.parameters) (key:lbytes (Hash.size_block p)) (len:size_t{Hash.size_block p + len < max_size_t /\ Hash.size_block p + len < Hash.maxInput p}) (data:lbytes len) =
  let nb = len / size_block p in
  let nr = len % size_block p in
  let nblocks8 = nb * size_block p in
  let l0 = slice data 0 nblocks8 in
  let l1 = slice data nblocks8 len in
  let hash0,key = init' p key in
  let hash1 = update_multi p nb l0 hash0 in
  let hash2 = update_last p (nb + 1) nr l1 hash1 in
  let mac = finish p key hash2 in
  mac


(* Core HMAC function for a key of length size_block *)
let hmac_core (p:Hash.parameters) (key:lbytes (Hash.size_block p)) (len:size_t{Hash.size_block p + len < max_size_t /\ Hash.size_block p + len < Hash.maxInput p}) (data:lbytes len) =

  (* Create the scratch space *)
  let s3  = create (Hash.size_block p + len) (u8 0x00) in
  let s6  = create (Hash.size_block p + p.size_hash) (u8 0x00) in

  (* Define ipad and opad *)
  let ipad = create (Hash.size_block p) (u8 0x36) in
  let opad = create (Hash.size_block p) (u8 0x5c) in

  (* Step 1: the key has the proper length *)
  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad key in

  (* Step 3: append data to "result of step 2" *)
  let s3 = update_slice s3 0 (Hash.size_block p) s2 in
  let s3 = update_slice s3 (Hash.size_block p) (Hash.size_block p + len) data in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Hash.hash p (Hash.size_block p + len) s3 in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = map2 (fun x y -> logxor x y) opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = update_slice s6 0 (Hash.size_block p) s5 in
  let s6 = update_slice s6 (Hash.size_block p) (Hash.size_block p + p.size_hash) s4 in

  (* Step 7: apply H to "result of step 6" *)
  Hash.hash p (p.size_hash + Hash.size_block p) s6


let hmac'
  (p:Hash.parameters)
  (klen:size_t)
  (key:lbytes klen)
  (len:size_t{Hash.size_block p + len < max_size_t /\ Hash.size_block p + len < Hash.maxInput p})
  (data:lbytes len) =

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key p klen key in

  (* Step 2-7: call hmac_core *)
  hmac_core' p okey len data


let hmac
  (p:Hash.parameters)
  (klen:size_t)
  (key:lbytes klen)
  (len:size_t{Hash.size_block p + len < max_size_t /\ Hash.size_block p + len < Hash.maxInput p})
  (data:lbytes len) =

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key p klen key in

  (* Step 2-7: call hmac_core *)
  hmac_core p okey len data
