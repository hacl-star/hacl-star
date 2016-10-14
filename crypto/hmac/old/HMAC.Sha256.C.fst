module HMAC.Sha256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
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

#set-options "--lax"

assume MaxU8: pow2 8 = 256
assume MaxU32: pow2 32 = 4294967296



let lemma_aux (#t:Type) h0 h1 h2 (b:buffer t) : Lemma
  (requires (modifies_0 h0 h1 /\ modifies_1 b h1 h2 /\ live h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip ))
  (ensures (modifies_0 h0 h2))
  = ()

let lemma_aux_2 (#t:Type) h2 hfin (mac:buffer t) : Lemma
  (requires (live h2 mac /\ popped h2 hfin /\ frameOf mac <> h2.tip ))
  (ensures  (live hfin mac))
  = ()


val xor_bytes: output:bytes -> in1:bytes -> in2:bytes{disjoint in1 in2 /\ disjoint in1 output /\ disjoint in2 output} -> len:u32{v len <= length output /\ v len <= length in1 /\ v len <= length in2} -> STL unit
  (requires (fun h -> live h output /\ live h in1 /\ live h in2))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h0 in2
    /\ live h1 output /\ live h1 in1 /\ live h1 in2
    /\ modifies_1 output h0 h1
    (* /\ (forall (i:nat). i < v len ==> get h1 output i = (UInt8.logxor (get h0 in1 i) (get h0 in2 i))) *)
   ))
let rec xor_bytes output in1 in2 len =
  let h0 = ST.get() in
  if len =^ 0ul then ()
  else
    begin
      let i = UInt32.sub len 1ul in
      let in1i = index in1 i in
      let in2i = index in2 i in
      let oi = Hacl.UInt8.logxor in1i in2i in
      upd output i oi;
      let h1 = ST.get() in
      no_upd_lemma_1 h0 h1 output in1;
      no_upd_lemma_1 h0 h1 output in2;
      xor_bytes output in1 in2 i
    end


(* Operators *)
let op_At_Plus (a:u32) (b:u32) : Tot u32 = UInt32.add a b
let op_At_Plus_Percent (a:u32) (b:u32) : Tot u32 = UInt32.add_mod a b


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


#reset-options "--z3timeout 100"


(* Define the main function *)
val hmac_sha256 : (mac     :bytes { length mac = v hl }) ->
                  (key     :bytes { disjoint key mac }) ->
                  (keylen  :u32   { length key = v keylen }) ->
                  (data    :bytes { disjoint mac data /\ disjoint key data }) ->
                  (datalen :u32   { length data = v datalen /\ v datalen + v bl <= pow2 32})
                  -> STL unit
                        (requires (fun h -> live h mac /\ live h data /\ live h key))
                        (ensures  (fun h0 r h1 -> live h1 mac /\ live h1 data /\ live h1 key /\ modifies_1 mac h0 h1))

let hmac_sha256 mac key keylen data datalen =
  
  (* Push a new frame *)
  (**) let hinit = ST.get() in
  (**) push_frame();
  (**) let h0 = ST.get() in

  (* Define ipad and opad *)
  let ipad = create (uint8_to_sint8 0x36uy) bl in
  let opad = create (uint8_to_sint8 0x5cuy) bl in

  (* Create the wrapped key location *)
  let okey = create (uint8_to_sint8 0uy) bl in
  (**) let h1 = ST.get() in
  (**) // assert(modifies_0 h0 h1);
  (**) no_upd_lemma_0 h0 h1 key;

  (* Step 1: make sure the key has the proper length *)
  wrap_key okey key keylen;
  (**) let h2 = ST.get() in
  (**) lemma_aux h0 h1 h2 okey;
  (**) //assert(modifies_0 h0 h2);
  (**) no_upd_lemma_0 h0 h2 mac;
  (**) no_upd_lemma_0 h0 h2 key;
  (**) no_upd_lemma_0 h0 h2 data;

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = create (uint8_to_sint8 0uy) bl in
  (**) let h3 = ST.get () in
  (**) //assert(modifies_0 h2 h3);
  (**) //assert(modifies_0 h0 h3);
  (**) no_upd_lemma_0 h2 h3 okey; 
  (**) no_upd_lemma_0 h2 h3 ipad;
  (**) no_upd_lemma_0 h2 h3 mac;
  (**) no_upd_lemma_0 h2 h3 key;
  (**) no_upd_lemma_0 h2 h3 data;

  xor_bytes s2 okey ipad bl;
  (**) let h4 = ST.get () in
  (**) lemma_aux h2 h3 h4 s2;
  (**) no_upd_lemma_1 h3 h4 s2 okey;
  (**) no_upd_lemma_1 h3 h4 s2 ipad;
  (**) //assert(modifies_0 h0 h4);
  (**) no_upd_lemma_0 h0 h4 mac;
  (**) no_upd_lemma_0 h0 h4 key;
  (**) no_upd_lemma_0 h0 h4 data;

  (* Step 3: append data to "result of step 2" *)
  let s3 = create (uint8_to_sint8 0uy) (bl @+ datalen) in
  (**) let h5 = ST.get () in
  (**) no_upd_lemma_0 h4 h5 s2;
  (**) //assert(modifies_0 h4 h5);
  (**) //assert(modifies_0 h0 h5);
  (**) //assert (length s3 >= (v bl) + (v datalen));
    
  blit s2 0ul s3 0ul bl;
  (**) let h6 = ST.get () in
  (**) //assert(modifies_1 s3 h5 h6);
  (**) lemma_aux h0 h5 h6 s3;
  (**) no_upd_lemma_1 h5 h6 s3 s2;
  (**) no_upd_lemma_0 h0 h6 mac;
  (**) no_upd_lemma_0 h0 h6 data;
  (**) no_upd_lemma_0 h0 h6 key;
  (**) assert(length s3 >= (v bl) + (v datalen));
    
  blit data 0ul s3 bl datalen;
  (**) let h7 = ST.get () in
  (**) //assert(modifies_1 s3 h6 h7);
  (**) lemma_aux h0 h6 h7 s3;
  (**) no_upd_lemma_1 h6 h7 s3 data;
  (**) //assert(live h7 s3);
  (**) assert(modifies_0 h0 h7);
  (**) no_upd_lemma_0 h0 h7 mac;
  (**) no_upd_lemma_0 h0 h7 data;
  (**) no_upd_lemma_0 h0 h7 key;
    
  (* Step 4: apply H to "result of step 3" *)
  let s4 = create (uint8_to_sint8 0uy) hl in
  (**) let h8 = ST.get () in
  (**) assert(modifies_0 h7 h8);
  (**) //assert(modifies_0 h0 h8);
  (**) no_upd_lemma_0 h0 h8 mac;
  (**) no_upd_lemma_0 h0 h8 data;
  (**) no_upd_lemma_0 h0 h8 key;
  (**) assert(live h8 s3);
  (**) assert(live h8 s4);
  (**) assert(disjoint s3 s4);
  (**) assert(v (bl @+ datalen) = length s3);
  (**) assert(length s4 >= v hl);

  hash s4 s3 (bl @+ datalen);
  (**) let h9 = ST.get () in
  (**) //assert(modifies_1 s4 h8 h9);
  (**) lemma_aux h0 h8 h9 s4;
  (**) no_upd_lemma_1 h8 h9 s4 s3;
  (**) no_upd_lemma_0 h0 h9 mac;
  (**) no_upd_lemma_0 h0 h9 data;
  (**) no_upd_lemma_0 h0 h9 key;
  // OK
    
  (* Step 5: xor "result of step 1" with opad *)
  let s5 = create (uint8_to_sint8 0uy) bl in
  (**) let h10 = ST.get () in
  (**) assert(modifies_0 h9 h10); admit()
  (**) assert(modifies_0 h0 h10);
  (**) no_upd_lemma_0 h0 h10 mac;
  (**) no_upd_lemma_0 h0 h10 data;
  (**) no_upd_lemma_0 h0 h10 key;

  xor_bytes s5 okey opad bl;
  (**) let h11 = ST.get() in
  (**) lemma_aux h9 h10 h11 s5;
  (**) no_upd_lemma_1 h10 h11 s5 okey;
  (**) no_upd_lemma_1 h10 h11 s5 opad;
  (**) assert(modifies_0 h0 h11);
  (**) no_upd_lemma_0 h0 h11 mac;
  (**) no_upd_lemma_0 h0 h11 key;
  (**) no_upd_lemma_0 h0 h11 data;

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = create (uint8_to_sint8 0uy) (hl @+ bl) in
    let h12 = ST.get () in
    assert(modifies_0 h11 h12);
    assert(modifies_0 h0 h12);
    no_upd_lemma_0 h0 h12 mac;
    no_upd_lemma_0 h0 h12 data;
    no_upd_lemma_0 h0 h12 key;

  blit s5 0ul s6 0ul bl;
    let h13 = ST.get () in
    assert(modifies_1 s6 h12 h13);
    lemma_aux h0 h12 h13 s6;
    assert(modifies_0 h0 h13);
    no_upd_lemma_0 h0 h13 mac;
    no_upd_lemma_0 h0 h13 data;
    no_upd_lemma_0 h0 h13 key;

  blit s4 0ul s6 bl hl;
    let h14 = ST.get () in
    assert(modifies_1 s6 h13 h14);
    lemma_aux h0 h13 h14 s6;
    assert(modifies_0 h0 h14);
    no_upd_lemma_0 h0 h14 mac;
    no_upd_lemma_0 h0 h14 data;
    no_upd_lemma_0 h0 h14 key;

  (* Step 7: apply H to "result of step 6" *)
  hash mac s6 (hl @+ bl);
    let h15 = ST.get () in
    assert(modifies_1 mac h14 h15);

  (* Pop frame *)
  pop_frame();
    let hfin = ST.get () in
    assert(modifies_1 mac hinit hfin);
    assume (equal_domains hinit hfin);
    assert(live hfin mac)
