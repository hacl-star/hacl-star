module Spec.HMAC

open FStar.Mul
open FStar.Seq
open FStar.UInt32

open Spec.Loops
open Spec.Lib

module U8 = FStar.UInt8

module Hash = Spec.HMAC.Hash


val pow2_values: x:nat -> Lemma
  (requires True)
  (ensures (let p = pow2 x in
   match x with
   | 61 -> p=2305843009213693952
   | _  -> True))
  [SMTPat (pow2 x)]
let pow2_values x =
   match x with
   | 61 -> assert_norm (pow2 61 == 2305843009213693952)
   | _  -> ()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 25"

(* Base types *)
type bytes = m:seq UInt8.t

private val xor_bytes: (b0:bytes) -> (b1:bytes{length b0 = length b1}) -> Tot bytes
let xor_bytes b0 b1 = Spec.Lib.map2 (fun x y -> U8.logxor x y) b0 b1


#reset-options "--max_fuel 0 --z3rlimit 25"

(* Define a function to wrap the key length after bl bits *)
let wrap_key (key:bytes) : GTot (okey:bytes{Seq.length okey = Hash.size_block}) =
  if Seq.length key > Hash.size_block then
    let nkey = Hash.hash key in
    Seq.append nkey (Seq.create (Hash.size_block - Hash.size_hash) 0uy)
  else
    Seq.append key (Seq.create (Hash.size_block - (Seq.length key)) 0uy)


(* Define the internal function *)
let hmac (key:bytes) (data:bytes) : GTot (mac:bytes{Seq.length mac = Hash.size_hash}) =

  (* Define ipad and opad *)
  let ipad = Seq.create Hash.size_block 0x36uy in
  let opad = Seq.create Hash.size_block 0x5cuy in

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key key in

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = xor_bytes ipad okey in

  (* Step 3: append data to "result of step 2" *)
  let s3 = Seq.append s2 data in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Hash.hash s3 in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = xor_bytes okey opad in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = Seq.append s5 s4 in

  (* Step 7: apply H to "result of step 6" *)
  Hash.hash s6
