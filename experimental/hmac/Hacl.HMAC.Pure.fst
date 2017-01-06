module Hacl.HMAC.Pure

module I8 = FStar.UInt8
module I32 = FStar.UInt32
module IB = FStar.Buffer
module HO = Hacl.Operations.Pure


(* Define base types *)
let i8 = FStar.UInt8.t
let i32 = FStar.UInt32.t
let buf32 = Seq.seq i32
let bytes = Seq.seq i8

(* Define algorithm parameters *)
module HM = Hash.SHA2.L256.Pure
let hash = HM.sha256
let hashsize = HM.hashsize
let blocksize = HM.blocksize
let hl = hashsize
let bl = blocksize


(* Define a function to wrap the key length after bl bits *)
let wrap_key (key:bytes) : GTot (okey:bytes{Seq.length okey = bl}) =
  if Seq.length key > bl then
    let okey = hash key in
    Seq.append okey (Seq.create (bl - hl) 0uy)
  else
    Seq.append key (Seq.create (bl - (Seq.length key)) 0uy)


(* Define the internal function *)
let hmac_core (key:bytes) (data:bytes) : GTot (mac:bytes{Seq.length mac = hashsize}) =

  (* Define ipad and opad *)
  let ipad = Seq.create bl 0x36uy in
  let opad = Seq.create bl 0x5cuy in

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key key in

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = HO.xor_bytes ipad okey bl in

  (* Step 3: append data to "result of step 2" *)
  let s3 = Seq.append s2 data in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = hash s3 in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = HO.xor_bytes okey opad bl in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = Seq.append s5 s4 in

  (* Step 7: apply H to "result of step 6" *)
  hash s6
