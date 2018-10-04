module Spec.HMAC

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32

open Spec.Compat.Loops
open Spec.Compat.Lib

module U8 = FStar.UInt8

module Hash = Spec.SHA2


#set-options "--max_fuel 0 --z3rlimit 10"

val xor_bytes: (b0:bytes) -> (b1:bytes{length b0 = length b1}) -> Tot bytes
let xor_bytes b0 b1 = Spec.Compat.Lib.map2 (fun x y -> U8.logxor x y) b0 b1


#reset-options "--max_fuel 0 --z3rlimit 25"

val wrap_key: a:Hash.Helpers.sha2_alg -> key:bytes{Seq.length key < Hash.Helpers.max_input8 a} -> Tot (okey:bytes{Seq.length okey = Hash.Helpers.size_block a})
let wrap_key a key =
  if Seq.length key <= Hash.Helpers.size_block a then
    let pad = Seq.create ((Hash.Helpers.size_block a) - (Seq.length key)) 0uy in
    Seq.append key pad
  else begin
    let nkey = Hash.Nist.hash a key in
    let pad = Seq.create ((Hash.Helpers.size_block a) - (Hash.Helpers.size_hash a)) 0uy in
    Seq.append nkey pad
  end


#reset-options "--max_fuel 0 --z3rlimit 10"

val hmac_core:
  a:Hash.Helpers.sha2_alg ->
  key  :bytes{Seq.length key = Hash.Helpers.size_block a} ->
  data :bytes{Seq.length data + Hash.Helpers.size_block a < Hash.Helpers.max_input8 a} ->
  Tot (mac:bytes{Seq.length mac = Hash.Helpers.size_hash a})

#reset-options "--max_fuel 0 --z3rlimit 50"

let hmac_core a key data =

  (* Define ipad and opad *)
  let ipad = Seq.create (Hash.Helpers.size_block a) 0x36uy in
  let opad = Seq.create (Hash.Helpers.size_block a) 0x5cuy in
  assert (Seq.length opad <= 128);

  (* Step 1: the key has the proper length *)
  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = xor_bytes ipad key in

  (* Step 3: append data to "result of step 2" *)
  let s3 = Seq.append s2 data in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Hash.Nist.hash a s3 in
  assert (Seq.length s4 = Hash.Helpers.size_hash a);
  assert (Seq.length s4 <= 128);

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = xor_bytes opad key in
  assert (Seq.length s5 <= 128);

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = Seq.append s5 s4 in
  assert (Seq.length s5 <= 256);
  (
    let open Spec.Hash.Helpers in
    match a with
    | SHA2_224 | SHA2_256 -> assert_norm (256 <= pow2 61)
    | SHA2_384 | SHA2_512 -> assert_norm (256 <= pow2 125));

  (* Step 7: apply H to "result of step 6" *)
  Hash.Nist.hash a s6


#reset-options "--max_fuel 0 --z3rlimit 10"

val hmac:
  a    :Hash.Helpers.sha2_alg ->
  key  :bytes{Seq.length key < Hash.Helpers.max_input8 a} ->
  data :bytes{Seq.length data + Hash.Helpers.size_block a < Hash.Helpers.max_input8 a} ->
  Tot (mac:bytes{Seq.length mac = Hash.Helpers.size_hash a})

#reset-options "--max_fuel 0 --z3rlimit 25"

let hmac a key data =

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key a key in

  (* Step 2-7: call hmac_core *)
  hmac_core a okey data
