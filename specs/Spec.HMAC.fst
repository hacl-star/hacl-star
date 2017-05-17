module Spec.HMAC

open FStar.Mul
open FStar.Seq
open FStar.UInt32

open Spec.Loops
open Spec.Lib

module U8 = FStar.UInt8

module Hash = Spec.HMAC.Hash


#set-options "--max_fuel 0 --z3rlimit 10"

(* Base types *)
type bytes = m:seq UInt8.t

private val xor_bytes: (b0:bytes) -> (b1:bytes{length b0 = length b1}) -> Tot bytes
let xor_bytes b0 b1 = Spec.Lib.map2 (fun x y -> U8.logxor x y) b0 b1


#reset-options "--max_fuel 0 --z3rlimit 25"

let wrap_key (key:bytes{Seq.length key < Hash.max_input_len_8}) : Tot (okey:bytes{Seq.length okey = Hash.size_block}) =
  if Seq.length key <= Hash.size_block then
    let pad = Seq.create (Hash.size_block - (Seq.length key)) 0uy in
    Seq.append key pad
  else begin
    let nkey = Hash.hash key in
    let pad = Seq.create (Hash.size_block - Hash.size_hash) 0uy in
    Seq.append nkey pad
  end


#reset-options "--max_fuel 0 --z3rlimit 10"

val hmac_core:
  key  :bytes{Seq.length key = Hash.size_block} ->
  data :bytes{Seq.length data + Hash.size_block < Hash.max_input_len_8} ->
  Tot (mac:bytes{Seq.length mac = Hash.size_hash})

#reset-options "--max_fuel 0 --z3rlimit 25"

let hmac_core key data =

  (* Define ipad and opad *)
  let ipad = Seq.create Hash.size_block 0x36uy in
  let opad = Seq.create Hash.size_block 0x5cuy in

  (* Step 1: the key has the proper length *)
  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = xor_bytes ipad key in

  (* Step 3: append data to "result of step 2" *)
  let s3 = Seq.append s2 data in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Hash.hash s3 in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = xor_bytes opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = Seq.append s5 s4 in

  (* Step 7: apply H to "result of step 6" *)
  Hash.hash s6


#reset-options "--max_fuel 0 --z3rlimit 10"

val hmac:
  key  :bytes{Seq.length key < Hash.max_input_len_8} ->
  data :bytes{Seq.length data + Hash.size_block < Hash.max_input_len_8} ->
  Tot (mac:bytes{Seq.length mac = Hash.size_hash})

#reset-options "--max_fuel 0 --z3rlimit 25"

let hmac key data =

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key key in

  (* Step 2-7: call hmac_core *)
  hmac_core okey data
