module Spec.HMAC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 25"

module Hash = Spec.Hash


(* Key wrapping function *)
let wrap_key (a:Hash.algorithm) (len:size_nat{len < Hash.max_input a}) (key:lbytes len) =
  let block = create (Hash.size_block a) (u8 0) in
  if len <= Hash.size_block a then
    update_slice block 0 len key
  else begin
    let nkey = Hash.hash a len key in
    update_slice block 0 (Hash.size_hash a) nkey
  end


let init (a:Hash.algorithm) (len:size_nat{len < Hash.max_input a}) (key:lbytes len) =

  (* Define ipad and opad *)
  let ipad = create (Hash.size_block a) (u8 0x36) in

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key a len key in

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad okey in

  (* Step 3a: feed s2 to the inner hash function *)
  let hash_w0 = Hash.update_block a s2 (Hash.init a) in
  hash_w0,okey


let init' (a:Hash.algorithm) (key:lbytes (Hash.size_block a)) =

  (* Define ipad and opad *)
  let ipad = create (Hash.size_block a) (u8 0x36) in

  (* Step 1: key already has the proper length *)
  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad key in

  (* Step 3a: feed s2 to the inner hash function *)
  let hash_w0 = Hash.update_block a s2 (Hash.init a) in
  hash_w0,key


let update_block (a:Hash.algorithm) (data:lbytes (Hash.size_block a)) (hash:Hash.state a) =
  Hash.update_block a data hash


let update_multi (a:Hash.algorithm) (n:size_nat{n * Hash.size_block a <= max_size_t}) (data:lbytes (n * Hash.size_block a)) (hash:Hash.state a) =
  Hash.update_multi a n data hash


let update_last (a:Hash.algorithm) (n:size_nat) (len:size_nat{len < Hash.size_block a /\ len + n * Hash.size_block a <= Hash.max_input a}) (last:lbytes len) (hash:Hash.state a) =
  Hash.update_last a len last hash


let finish (a:Hash.algorithm) (key:lbytes (Hash.size_block a)) (hash:Hash.state a) =

  (* Define opad *)
  let opad = create (Hash.size_block a) (u8 0x5c) in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Hash.finish a hash in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = map2 (fun x y -> logxor x y) opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  let hash0 = Hash.update_block a s5 (Hash.init a) in
  let hash1 = Hash.update_last a (Hash.size_hash a) s4 hash0 in
  let hash2 = Hash.finish a hash1 in
  hash2


(* Core HMAC function for a key of length size_block *)
let hmac_core' (a:Hash.algorithm) (key:lbytes (Hash.size_block a)) (len:size_nat{Hash.size_block a + len <= max_size_t /\ Hash.size_block a + len < Hash.max_input a}) (data:lbytes len) =
  let nb = len / Hash.size_block a in
  let nr = len % Hash.size_block a in
  let nblocks8 = nb * Hash.size_block a in
  let l0 = slice data 0 nblocks8 in
  let l1 = slice data nblocks8 len in
  let hash0,key = init' a key in
  let hash1 = update_multi a nb l0 hash0 in
  let hash2 = update_last a (nb + 1) nr l1 hash1 in
  let mac = finish a key hash2 in
  mac


(* Core HMAC function for a key of length size_block *)
let hmac_core (a:Hash.algorithm) (key:lbytes (Hash.size_block a)) (len:size_nat{Hash.size_block a + len <= max_size_t /\ Hash.size_block a + len < Hash.max_input a}) (data:lbytes len) =

  (* Create the scratch space *)
  let s3  = create (Hash.size_block a + len) (u8 0x00) in
  let s6  = create (Hash.size_block a + Hash.size_hash a) (u8 0x00) in

  (* Define ipad and opad *)
  let ipad = create (Hash.size_block a) (u8 0x36) in
  let opad = create (Hash.size_block a) (u8 0x5c) in

  (* Step 1: the key has the proper length *)
  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = map2 (fun x y -> logxor x y) ipad key in

  (* Step 3: append data to "result of step 2" *)
  let s3 = update_slice s3 0 (Hash.size_block a) s2 in
  let s3 = update_slice s3 (Hash.size_block a) (Hash.size_block a + len) data in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Hash.hash a (Hash.size_block a + len) s3 in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = map2 (fun x y -> logxor x y) opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = update_slice s6 0 (Hash.size_block a) s5 in
  let s6 = update_slice s6 (Hash.size_block a) (Hash.size_block a + Hash.size_hash a) s4 in

  (* Step 7: apply H to "result of step 6" *)
  Hash.hash a (Hash.size_hash a + Hash.size_block a) s6


let hmac'
  (a:Hash.algorithm)
  (klen:size_nat{klen < Hash.max_input a})
  (key:lbytes klen)
  (len:size_nat{Hash.size_block a + len <= max_size_t /\ Hash.size_block a + len < Hash.max_input a})
  (data:lbytes len) =

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key a klen key in

  (* Step 2-7: call hmac_core *)
  hmac_core' a okey len data


let hmac
  (a:Hash.algorithm)
  (klen:size_nat{klen < Hash.max_input a})
  (key:lbytes klen)
  (len:size_nat{Hash.size_block a + len <= max_size_t /\ Hash.size_block a + len < Hash.max_input a})
  (data:lbytes len) =

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key a klen key in

  (* Step 2-7: call hmac_core *)
  hmac_core a okey len data


///
/// Instances for HMAC SHA2
///

let wrap_key224 = wrap_key Hash.SHA2_224
let wrap_key256 = wrap_key Hash.SHA2_256
let wrap_key384 = wrap_key Hash.SHA2_384
let wrap_key512 = wrap_key Hash.SHA2_512

let init224 = init Hash.SHA2_224
let init256 = init Hash.SHA2_256
let init384 = init Hash.SHA2_384
let init512 = init Hash.SHA2_512

let init'224 = init' Hash.SHA2_224
let init'256 = init' Hash.SHA2_256
let init'384 = init' Hash.SHA2_384
let init'512 = init' Hash.SHA2_512

let update_block224 = update_block Hash.SHA2_224
let update_block256 = update_block Hash.SHA2_256
let update_block384 = update_block Hash.SHA2_384
let update_block512 = update_block Hash.SHA2_512

let update_multi224 = update_multi Hash.SHA2_224
let update_multi256 = update_multi Hash.SHA2_256
let update_multi384 = update_multi Hash.SHA2_384
let update_multi512 = update_multi Hash.SHA2_512

let update_last224 = update_last Hash.SHA2_224
let update_last256 = update_last Hash.SHA2_256
let update_last384 = update_last Hash.SHA2_384
let update_last512 = update_last Hash.SHA2_512

let finish224 = finish Hash.SHA2_224
let finish256 = finish Hash.SHA2_256
let finish384 = finish Hash.SHA2_384
let finish512 = finish Hash.SHA2_512

let hmac_core224 = hmac_core Hash.SHA2_224
let hmac_core256 = hmac_core Hash.SHA2_256
let hmac_core384 = hmac_core Hash.SHA2_384
let hmac_core512 = hmac_core Hash.SHA2_512

let hmac224' = hmac' Hash.SHA2_224
let hmac256' = hmac' Hash.SHA2_256
let hmac384' = hmac' Hash.SHA2_384
let hmac512' = hmac' Hash.SHA2_512

let hmac224 = hmac Hash.SHA2_224
let hmac256 = hmac Hash.SHA2_256
let hmac384 = hmac Hash.SHA2_384
let hmac512 = hmac Hash.SHA2_512
