module HMAC.Sha1

open FStar.Heap
open SBytes
open SBuffer
open SInt.UInt8
open Hash.Sha1



(* Define parameters *)
let hash = sha1
let hl = 20
let bl = 64

(* Define a function to wrap the key length after bl bits *)
val wrap_key : (key    :sbytes) ->
               (keylen :nat { length key = keylen })
               -> St (okey:sbytes { length okey <= bl } * okeylen: nat)

let wrap_key key keylen =
  if keylen > bl then
    let nkey = create #8 SInt.UInt8.zero hl in
    hash nkey key keylen;
    nkey,hl
  else
    key,keylen


(* Define the main function *)
val hmac_sha1 : (mac     :sbytes { length mac = hl }) ->
                (key     :sbytes { disjoint key mac }) ->
                (keylen  :nat      { length key = keylen }) ->
                (data    :sbytes { disjoint mac data /\ disjoint key data }) ->
                (datalen :nat      { length data = datalen })
                -> ST unit
                     (requires (fun h -> live h mac /\ live h data /\ live h key))
                     (ensures  (fun h0 r h1 -> live h1 mac /\ live h1 data /\ live h1 key))

let hmac_sha1 mac key keylen data datalen =
  (* Define ipad and opad *)
  let ipad = SBuffer.create #8 (SInt.UInt8.of_string "0x36") bl in
  let opad = SBuffer.create #8 (SInt.UInt8.of_string "0x5c") bl in

  (* Step 1: make sure the key has the proper length *)
  let okey,okeylen = wrap_key key keylen in
  let s1 = create #8 SInt.UInt8.zero bl in
  SBytes.blit okey 0 s1 0 okeylen;

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = create #8 SInt.UInt8.zero bl in
  SBytes.xor_bytes s2 s1 ipad bl;

  (* Step 3: append data to "result of step 2" *)
  let s3 = create #8 SInt.UInt8.zero (bl + datalen) in
  SBytes.blit s2 0 s3 0 bl;
  SBytes.blit data 0 s3 bl datalen;

  (* Step 4: apply H to "result of step 3" *)
  let s4 = create #8 SInt.UInt8.zero hl in
  hash s4 s3 (bl + datalen);

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = create #8 SInt.UInt8.zero bl in
  SBytes.xor_bytes s5 s1 opad bl;

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = create #8 SInt.UInt8.zero (hl + bl) in
  SBytes.blit s5 0 s6 0 bl;
  SBytes.blit s4 0 s6 bl hl;

  (* Step 7: apply H to "result of step 6" *)
  hash mac s6 (hl + bl)
