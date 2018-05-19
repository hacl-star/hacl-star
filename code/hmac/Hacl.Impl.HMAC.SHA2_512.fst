module Hacl.Impl.HMAC.SHA2_512

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Buffer

open C.Loops

open Hacl.Spec.Endianness
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


(* Definition of aliases for modules *)
module ST = FStar.HyperStack.ST
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module Spec_Hash = Spec.SHA2_512
module Hash = Hacl.Impl.SHA2_512
module Spec = Spec.HMAC.SHA2_512


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t

private let uint32_p = Buffer.buffer uint32_ht
private let uint8_p  = Buffer.buffer uint8_ht


(* Definitions of aliases for functions *)
[@"substitute"]
private let u8_to_h8 = Hacl.Cast.uint8_to_sint8
[@"substitute"]
private let u32_to_h32 = Hacl.Cast.uint32_to_sint32
[@"substitute"]
private let u32_to_h64 = Hacl.Cast.uint32_to_sint64
[@"substitute"]
private let h32_to_h8  = Hacl.Cast.sint32_to_sint8
[@"substitute"]
private let h32_to_h64 = Hacl.Cast.sint32_to_sint64
[@"substitute"]
private let u64_to_h64 = Hacl.Cast.uint64_to_sint64


//
// HMAC-SHA2-512
//

#reset-options "--max_fuel 0  --z3rlimit 10"

let xor_bytes_inplace a b len = C.Loops.in_place_map2 a b len (fun x y -> H8.logxor x y)


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val wrap_key:
  output :uint8_p  {length output = v Hash.size_block} ->
  key    :uint8_p  {disjoint output key} ->
  len    :uint32_t {v len = length key /\ v len < Spec_Hash.max_input_len_8} ->
  Stack unit
        (requires (fun h -> live h output /\ live h key /\
                  reveal_sbytes (as_seq h output) == Seq.create (v Hash.size_block) 0uy))
        (ensures  (fun h0 _ h1 -> live h1 output /\ live h1 key /\ live h0 output /\ live h0 key /\ modifies_1 output h0 h1
                  /\ reveal_sbytes (as_seq h0 output) == Seq.create (v Hash.size_block) 0uy
                  /\ reveal_sbytes (as_seq h1 output) == Spec.wrap_key (reveal_sbytes (as_seq h0 key))))

#reset-options "--max_fuel 0  --z3rlimit 250"

[@"substitute"]
let wrap_key output key len =
 (**) let h0 = ST.get () in
  if len <=^ Hash.size_block then begin
    (**) assert(v Hash.size_block - v len >= 0);
    (**) assert(reveal_sbytes (as_seq h0 output) == Seq.create (v Hash.size_block) 0uy);
    Buffer.blit key 0ul output 0ul len;
    (**) let h1 = ST.get () in
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h1 output) 0 (v len)) (as_seq h0 key);
    (**) assert(Seq.slice (as_seq h1 output) 0 (v len) == as_seq h0 key);
    (**) Seq.lemma_eq_intro (reveal_sbytes (Seq.slice (as_seq h1 output) (v len) (v Hash.size_block))) (Seq.create (v Hash.size_block - v len) 0uy);
    (**) assert(reveal_sbytes (Seq.slice (as_seq h1 output) (v len) (v Hash.size_block)) == Seq.create (v Hash.size_block - v len) 0uy);
    (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 output)) (Seq.append (reveal_sbytes (as_seq h0 key)) (Seq.create (v Hash.size_block - v len) 0uy));
    (**) assert(reveal_sbytes (as_seq h1 output) == Seq.append (reveal_sbytes (as_seq h0 key)) (Seq.create (v Hash.size_block - v len) 0uy)) end
  else begin
    (**) assert(v Hash.size_block - v Hash.size_hash >= 0);
    (**) assert(reveal_sbytes (as_seq h0 output) == Seq.create (v Hash.size_block) 0uy);
    (**) Seq.lemma_eq_intro (Seq.slice (reveal_sbytes (as_seq h0 output)) 0 (v Hash.size_hash)) (Seq.create (v Hash.size_hash) 0uy);
    (**) assert(Seq.slice (reveal_sbytes (as_seq h0 output)) 0 (v Hash.size_hash) == Seq.create (v Hash.size_hash) 0uy);
    (**) Seq.lemma_eq_intro (Seq.slice (reveal_sbytes (as_seq h0 output)) (v Hash.size_hash) (v Hash.size_block)) (Seq.create (v Hash.size_block - v Hash.size_hash) 0uy);
    (**) assert(Seq.slice (reveal_sbytes (as_seq h0 output)) (v Hash.size_hash) (v Hash.size_block) == Seq.create (v Hash.size_block - v Hash.size_hash) 0uy);
    let nkey = Buffer.sub output 0ul Hash.size_hash in
    Hash.hash nkey key len;
    (**) let h1' = ST.get () in
    (**) assert(reveal_sbytes (as_seq h1' nkey) == Spec_Hash.hash (reveal_sbytes (as_seq h0 key)));
    (**) assert(Seq.slice (reveal_sbytes (as_seq h1' output)) 0 (v Hash.size_hash) == Spec_Hash.hash (reveal_sbytes (as_seq h0 key)));
    (**) no_upd_lemma_1 h0 h1' (Buffer.sub output 0ul Hash.size_hash) (Buffer.sub output Hash.size_hash (Hash.size_block -^ Hash.size_hash));
    (**) Seq.lemma_eq_intro (Seq.slice (reveal_sbytes (as_seq h1' output)) (v Hash.size_hash) (v Hash.size_block)) (Seq.create (v Hash.size_block - v Hash.size_hash) 0uy);
    (**) assert(Seq.slice (reveal_sbytes (as_seq h1' output)) (v Hash.size_hash) (v Hash.size_block) == Seq.create (v Hash.size_block - v Hash.size_hash) 0uy);
    (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h1' output)) (Seq.append (reveal_sbytes (as_seq h1' nkey)) (Seq.create (v Hash.size_block - v Hash.size_hash) 0uy));
    (**) assert(reveal_sbytes (as_seq h1' output) == Seq.append (reveal_sbytes (as_seq h1' nkey)) (Seq.create (v Hash.size_block - v Hash.size_hash) 0uy))
  end


#reset-options "--max_fuel 0  --z3rlimit 50"

val lemma_alloc:
  s:Seq.seq UInt32.t{Seq.length s = UInt32.v Hash.size_state} ->
  Lemma (requires (s == Seq.create (UInt32.v Hash.size_state) 0ul))
        (ensures (let seq_counter = Seq.slice s (U32.v Hash.pos_count_w) (U32.(v Hash.pos_count_w + v Hash.size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              U32.v counter = 0))
let lemma_alloc s = ()


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val hmac_part1:
  s2     :uint8_p {length s2 = v Hash.size_block} ->
  data   :uint8_p  {length data + v Hash.size_block < pow2 32 /\ disjoint data s2} ->
  len    :uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h ->  live h s2 /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 s2 /\ live h0 s2
                             /\ live h1 data /\ live h0 data /\ modifies_1 s2 h0 h1
                             /\ (let hash0 = Seq.slice (reveal_sbytes (as_seq h1 s2)) 0 (v Hash.size_hash) in
                             hash0 == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s2)) (reveal_sbytes (as_seq h0 data))))))

#reset-options "--max_fuel 0  --z3rlimit 200"

[@"substitute"]
let hmac_part1 s2 data len =
  (**) let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get () in

  (* Allocate memory for the Hash function state *)
  // let state0 = Hash.alloc () in
  let state0 = Buffer.create (u32_to_h32 0ul) Hash.size_state in
  (**) let h = ST.get() in
  (**) lemma_alloc (reveal_h32s (as_seq h state0));
  (**) no_upd_lemma_0 h0 h s2;
  (**) no_upd_lemma_0 h0 h data;

  (* Step 3: append data to "result of step 2" *)
  (* Step 4: apply Hash to "result of step 3" *)
  (**) assert(Hash.size_block <> 0ul);
  (**) Math.Lemmas.lemma_div_mod (v len) (v Hash.size_block);
  let n0 = U32.div len Hash.size_block in
  let r0 = U32.rem len Hash.size_block in
  let blocks0 = Buffer.sub data 0ul (n0 *^ Hash.size_block) in
  let last0 = Buffer.offset data (n0 *^ Hash.size_block) in
  (**) lemma_disjoint_sub data last0 state0;
  (**) lemma_disjoint_sub data blocks0 state0;
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h data) 0 (U32.v (n0 *^ Hash.size_block))) (as_seq h blocks0);
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h data) (U32.v (n0 *^ Hash.size_block)) (length data)) (as_seq h last0);
  Hash.init state0;
  (**) let h' = ST.get() in
  (**) no_upd_lemma_1 h h' state0 s2;
  (**) no_upd_lemma_1 h h' state0 data;
  (**) no_upd_lemma_1 h h' state0 blocks0;
  (**) no_upd_lemma_1 h h' state0 last0;
  Hash.update state0 s2;
  (**) let h'' = ST.get() in
  (**) lemma_modifies_1_trans state0 h h' h'';
  (**) no_upd_lemma_1 h' h'' state0 blocks0;
  (**) no_upd_lemma_1 h' h'' state0 last0;
  Hash.update_multi state0 blocks0 n0;
  (**) let h''' = ST.get() in
  (**) lemma_modifies_1_trans state0 h h'' h''';
  (**) no_upd_lemma_1 h'' h''' state0 last0;
  Hash.update_last state0 last0 r0;
  (**) let h1 = ST.get () in
  (**) lemma_modifies_1_trans state0 h h''' h1;
  (**) lemma_modifies_0_1' state0 h0 h h1;

  let h'''' = ST.get() in
  let hash0 = Buffer.sub s2 0ul Hash.size_hash in (* Salvage memory *)
  Hash.finish state0 hash0; (* s4 = hash (s2 @| data) *)
  (**) let h2 = ST.get() in
  (**) modifies_subbuffer_1 h1 h2 hash0 s2;
  (**) lemma_modifies_0_1 s2 h0 h1 h2;
//  (**) Spec_Hash.lemma_hash_all_prepend_block (reveal_sbytes (as_seq h0 s2)) (reveal_sbytes (as_seq h0 data));

  (* Pop the memory frame *)
  (**) pop_frame ();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 s2 hinit h0 h2 hfin

#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val hmac_part2:
  mac :uint8_p {length mac = v Hash.size_hash} ->
  s5  :uint8_p {length s5 = v Hash.size_block /\ disjoint s5 mac} ->
  s4  :uint8_p {length s4 = v Hash.size_hash /\ disjoint s4 mac /\ disjoint s4 s5} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h s5 /\ live h s4))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 s5 /\ live h0 s5
                             /\ live h1 s4 /\ live h0 s4 /\ modifies_1 mac h0 h1
                             /\ (reveal_sbytes (as_seq h1 mac) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))))))

#reset-options "--max_fuel 0  --z3rlimit 200"

[@"substitute"]
let hmac_part2 mac s5 s4 =
  assert_norm(pow2 32 = 0x100000000);
  let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get () in

  (* Allocate memory for the Hash function state *)
  (* let state1 = Hash.alloc () in *)
  let state1 = Buffer.create (u32_to_h32 0ul) Hash.size_state in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  (**) let h = ST.get() in
  (**) no_upd_lemma_0 h0 h s5;
  (**) no_upd_lemma_0 h0 h s4;
  (**) no_upd_lemma_0 h0 h mac;
  (**) lemma_alloc (reveal_h32s (as_seq h state1));
  Hash.init state1;
  (**) let h' = ST.get() in
  (**) assert(
       let st_h0 = Seq.slice (as_seq h' state1) (U32.v Hash.pos_whash_w) (U32.(v Hash.pos_whash_w + v Hash.size_whash_w)) in
       reveal_h32s st_h0 == Spec_Hash.h_0);
  (**) no_upd_lemma_1 h h' state1 s5;
  (**) no_upd_lemma_1 h h' state1 s4;
  (**) no_upd_lemma_1 h h' state1 mac;
  Hash.update state1 s5; (* s5 = opad *)
  (**) let h'' = ST.get() in
  (**) lemma_modifies_1_trans state1 h h' h'';
  (**) assert(
       let st_h0 = Seq.slice (as_seq h'' state1) (U32.v Hash.pos_whash_w) (U32.(v Hash.pos_whash_w + v Hash.size_whash_w)) in
       reveal_h32s st_h0 == Spec_Hash.(update h_0 (reveal_sbytes (as_seq h0 s5))));
  (**) no_upd_lemma_1 h' h'' state1 s4;
  (**) no_upd_lemma_1 h' h'' state1 mac;
  (**) assert(as_seq h'' s4 == as_seq hinit s4);
  Hash.update_last state1 s4 Hash.size_hash;
  (**) let h''' = ST.get() in
  (**) lemma_modifies_1_trans state1 h h'' h''';
  (**) lemma_modifies_0_1' state1 h0 h h''';
  (**) no_upd_lemma_1 h' h'' state1 s4;
  (**) no_upd_lemma_1 h' h'' state1 mac;
  (**) assert(live h''' mac);
  Hash.finish state1 mac; //(* s7 = hash (s5 @| s4) *)
  (**) let h1 = ST.get() in
  (**) lemma_modifies_0_1 mac h0 h''' h1;
//  (**) Spec_Hash.lemma_hash_single_prepend_block (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 mac)) (Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))));
  (**) assert(reveal_sbytes (as_seq h1 mac) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))));
  (* Pop the memory frame *)
  (**) pop_frame ();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 mac hinit h0 h1 hfin


#reset-options "--max_fuel 0  --z3rlimit 20"

val hmac_core:
  mac  :uint8_p  {length mac = v Hash.size_hash} ->
  key  :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  data :uint8_p  {length data + v Hash.size_block < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  len  :uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1
                             /\ (reveal_sbytes (as_seq h1 mac) == Spec.hmac_core (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)))))

#reset-options "--max_fuel 0  --z3rlimit 150"

let hmac_core mac key data len =

  let h00 = ST.get () in
  let hinit = h00 in
  (* Push a new memory frame *)
  (**) push_frame ();
  let h0 = ST.get () in

  (* Initialize constants *)
  let ipad = Buffer.create (u8_to_h8 0x36uy) Hash.size_block in
  (**) let h0' = ST.get() in  
  let opad = Buffer.create (u8_to_h8 0x5cuy) Hash.size_block in
  (**) let h1 = ST.get () in
  (**) lemma_modifies_0_0 h0 h0' h1;
  (**) assert(reveal_sbytes (as_seq h1 ipad) == Seq.create (v Hash.size_block) 0x36uy);
  (**) assert(reveal_sbytes (as_seq h1 opad) == Seq.create (v Hash.size_block) 0x5cuy);

  (* Step 2: xor "result of step 1" with ipad *)
  xor_bytes_inplace ipad key Hash.size_block;
  (**) let h2 = ST.get () in
  (**) lemma_modifies_0_1' ipad h0 h1 h2;
  (**) assert(reveal_sbytes (as_seq h2 ipad) == Spec.xor_bytes (reveal_sbytes (as_seq h1 ipad)) (reveal_sbytes (as_seq h0 key)));

  (* Step 3: append data to "result of step 2" *)
  (* Step 4: apply Hash to "result of step 3" *)
  hmac_part1 ipad data len; (* s2 = ipad *)
  let s4 = Buffer.sub ipad 0ul Hash.size_hash in (* Salvage memory *)
  (**) let h3 = ST.get () in
  (**) lemma_modifies_0_1' ipad h0 h2 h3;
  (**) Seq.lemma_eq_intro (as_seq h3 (Buffer.sub ipad 0ul Hash.size_hash)) (Seq.slice (as_seq h3 ipad) 0 (v Hash.size_hash));
  (**) assert(reveal_sbytes (as_seq h3 s4) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h2 ipad)) (reveal_sbytes (as_seq h0 data))));
  (**) assert(reveal_sbytes (as_seq h3 s4) == Spec_Hash.hash (Seq.append (Spec.xor_bytes (reveal_sbytes (as_seq h1 ipad)) (reveal_sbytes (as_seq h0 key))) (reveal_sbytes (as_seq h0 data))));

  (* Step 5: xor "result of step 1" with opad *)
  xor_bytes_inplace opad key Hash.size_block;
  (**) let h4 = ST.get () in
  (**) lemma_modifies_0_1' opad h0 h3 h4;
  (**) assert(reveal_sbytes (as_seq h4 opad) == Spec.xor_bytes (reveal_sbytes (as_seq h1 opad)) (reveal_sbytes (as_seq h0 key)));

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  hmac_part2 mac opad s4; (* s5 = opad *)
  (**) let h5 = ST.get () in
  (**) lemma_modifies_0_1 mac h0 h4 h5;
  (**) assert(reveal_sbytes (as_seq h5 mac) == Spec.hmac_core (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)));

  (* Pop the memory frame *)
  (**) pop_frame ();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 mac hinit h0 h5 hfin


#reset-options "--max_fuel 0  --z3rlimit 20"

val hmac:
  mac     :uint8_p  {length mac = v Hash.size_hash} ->
  key     :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  keylen  :uint32_t {v keylen = length key} ->
  data    :uint8_p  {length data + v Hash.size_block < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  datalen :uint32_t {v datalen = length data} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1
                             /\ (reveal_sbytes (as_seq h1 mac) == Spec.hmac (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)))))

#reset-options "--max_fuel 0  --z3rlimit 25"

let hmac mac key keylen data datalen =

  (**) let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get() in

  (* Allocate memory for the wrapped key *)
  let nkey = Buffer.create (u8_to_h8 0x00uy) Hash.size_block in
  (**) let h1 = ST.get() in

  (* Call the key wrapping function *)
  wrap_key nkey key keylen;
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_1' nkey h0 h1 h2;

  (* Call the core HMAC function *)
  hmac_core mac nkey data datalen;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1 mac h0 h2 h3;

  (* Pop the memory frame *)
  (**) pop_frame ();

  (**) let hfin = ST.get() in
  (**) modifies_popped_1 mac hinit h0 h3 hfin
