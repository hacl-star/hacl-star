module HMAC.Sha256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer

open Hash.Sha256


module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module U8 = Hacl.UInt8
module U32 = Hacl.UInt32

let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s


assume MaxU8: pow2 8 = 256
assume MaxU32: pow2 32 = 4294967296

val xor_bytes: output:bytes -> in1:bytes -> in2:bytes{disjoint in1 in2 /\ disjoint in1 output /\ disjoint in2 output} -> len:u32{v len <= length output /\ v len <= length in1 /\ v len <= length in2} -> STL unit
  (requires (fun h -> live h output /\ live h in1 /\ live h in2))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h0 in2 
    /\ live h1 output /\ live h1 in1 /\ live h1 in2
    /\ modifies_1 output h0 h1
    (* /\ (forall (i:nat). i < v len ==> get h1 output i = (UInt8.logxor (get h0 in1 i) (get h0 in2 i))) *)
   ))
let rec xor_bytes output in1 in2 len =
  let h0 = HST.get() in
  if len =^ 0ul then ()
  else
    begin
      let i = UInt32.sub len 1ul in 
      let in1i = index in1 i in
      let in2i = index in2 i in
      let oi = Hacl.UInt8.logxor in1i in2i in
      upd output i oi; 
      let h1 = HST.get() in
      no_upd_lemma_1 h0 h1 output in1;
      no_upd_lemma_1 h0 h1 output in2;
      xor_bytes output in1 in2 i
    end


(* Operators *)
let op_At_Plus (a:u32) (b:u32) : Tot u32 = UInt32.add_mod a b


(* Define parameters *)
let hash = Hash.Sha256.sha256
let hl = 32ul
let bl = 64ul


(* Define a function to wrap the key length after bl bits *)
val wrap_key : (okey:bytes{ length okey = v bl}) -> (key:bytes {disjoint okey key}) -> (keylen :u32 { length key = v keylen })
               -> STL unit
                     (requires (fun h -> live h okey /\ live h key))
                     (ensures  (fun h0 _ h1 -> live h1 okey /\ live h1 key /\ modifies_1 okey h0 h1))

let wrap_key okey key keylen =
  if gt keylen bl then
    hash okey key keylen
  else
    blit key 0ul okey 0ul keylen


(* Define the main function *)
val hmac_sha256 : (mac     :bytes { length mac = v hl }) ->
                  (key     :bytes { disjoint key mac }) ->
                  (keylen  :u32   { length key = v keylen }) ->
                  (data    :bytes { disjoint mac data /\ disjoint key data }) ->
                  (datalen :u32   { length data = v datalen })
                  -> STL unit
                        (requires (fun h -> live h mac /\ live h data /\ live h key))
                        (ensures  (fun h0 r h1 -> live h1 mac /\ live h1 data /\ live h1 key /\ modifies_1 mac h0 h1))

let hmac_sha256 mac key keylen data datalen =
  (* Define ipad and opad *)
  let ipad = create (uint8_to_sint8 0x36uy) bl in
  let opad = create (uint8_to_sint8 0x5cuy) bl in

  (* Create the wrapped key location *)
  let okey = create (uint8_to_sint8 0uy) bl in

  (* Step 1: make sure the key has the proper length *)
  wrap_key okey key keylen;

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = create (uint8_to_sint8 0uy) bl in
  xor_bytes s2 okey ipad bl;

  (* Step 3: append data to "result of step 2" *)
  let s3 = create (uint8_to_sint8 0uy) (bl @+ datalen) in
  blit s2 0ul s3 0ul bl;
  blit data 0ul s3 bl datalen;

  (* Step 4: apply H to "result of step 3" *)
  let s4 = create (uint8_to_sint8 0uy) hl in
  hash s4 s3 (bl @+ datalen);

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = create (uint8_to_sint8 0uy) bl in
  xor_bytes s5 okey opad bl;

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = create (uint8_to_sint8 0uy) (hl @+ bl) in
  blit s5 0ul s6 0ul bl;
  blit s4 0ul s6 bl hl;

  (* Step 7: apply H to "result of step 6" *)
  hash mac s6 (hl @+ bl)
