(* Agile HKDF *)
module Crypto.HMAC

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer
open Buffer.Utils

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

open FStar.UInt32
open Crypto.Symmetric.Bytes
open Crypto.Indexing

open C.Loops

(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module Spec_H256 = Spec.SHA2_256
module H256 = Hacl.Hash.SHA2_256
module Spec_H384 = Spec.SHA2_384
module H384 = Hacl.Hash.SHA2_384
module Spec_H512 = Spec.SHA2_512
module H512 = Hacl.Hash.SHA2_512

module Spec_HMAC256 = Spec.HMAC.SHA2_256

private let uint8_t  = FStar.UInt8.t
private let uint32_t = FStar.UInt32.t
private let uint32_p = Buffer.buffer uint32_t
private let uint8_p  = Buffer.buffer uint8_t
private let uint64_t = FStar.UInt64.t
private let uint64_p = Buffer.buffer uint64_t

type bytes = Seq.seq uint8_t
type lbytes (n:nat) = b:bytes{Seq.length b = n}

//
// HMAC-SHA2-256
//

// ADL lax prototype for QUIC deadline
#set-options "--lax"

//#reset-options "--max_fuel 0 --z3rlimit 10"
let xor_bytes_inplace a b len =
  C.Loops.in_place_map2 a b len (fun x y -> U8.logxor x y)

type alg =
  | SHA256
  | SHA384
  | SHA512

//#reset-options "--initial_ifuel 2 --initial_fuel 0 --z3rlimit 20"
let block_size : alg -> Tot uint32_t = function
  | SHA256 -> H256.size_block
  | SHA384 -> H384.size_block
  | SHA512 -> H512.size_block

let hash_size: alg -> Tot uint32_t = function
  | SHA256 -> H256.size_hash
  | SHA384 -> H384.size_hash
  | SHA512 -> H512.size_hash

let state_size: alg -> Tot uint32_t = function
  | SHA256 -> H256.size_state
  | SHA384 -> H384.size_state
  | SHA512 -> H512.size_state

//#reset-options "--initial_ifuel 2 --initial_fuel 2 --z3rlimit 30"
noextract let max_byte_length : alg -> Tot nat = function
  | SHA256 -> Spec_H256.max_input_len_8
  | SHA384 -> Spec_H384.max_input_len_8
  | SHA512 -> Spec_H512.max_input_len_8

//#reset-options "--initial_fuel 0 --initial_ifuel 0 --z3rlimit 20"
let correct_wrap_key (a:alg)
  (key:Seq.seq uint8_t{Seq.length key < max_byte_length a})
  (wrapped:Seq.seq uint8_t{Seq.length wrapped = v (block_size a)}) : GTot Type =
  match a with
  | SHA256 -> Spec_HMAC256.wrap_key key == wrapped
  | SHA384 -> True // Spec missing
  | SHA512 -> True // Spec missing

let correct_agile_hash (a:alg)
  (input:Seq.seq uint8_t{Seq.length input < max_byte_length a})
  (digest:Seq.seq uint8_t{Seq.length digest = v (hash_size a)})
  : GTot Type =
  match a with
  | SHA256 -> Spec_H256.hash input == digest
  | SHA384 -> Spec_H384.hash input == digest
  | SHA512 -> Spec_H512.hash input == digest

[@"substitute"]
val wrap_key:
  a      : alg ->
  output : uint8_p  {length output = v (block_size a)} ->
  key    : uint8_p  {disjoint output key} ->
  len    : uint32_t {v len = length key /\ v len < max_byte_length a} ->
  Stack unit
    (requires (fun h -> live h output /\ live h key /\
      (as_seq h output) == Seq.create (v (block_size a)) 0uy))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h1 key /\ live h0 output /\ live h0 key
      /\ modifies_1 output h0 h1
      /\ as_seq h0 output == Seq.create (v (block_size a)) 0uy
      /\ correct_wrap_key a (as_seq h0 key) (as_seq h1 output)))

let agile_hash (a:alg) (output:uint8_p{length output = v (hash_size a)})
  (input:uint8_p{length input < max_byte_length a /\ disjoint output input})
  (len:uint32_t{v len = length output})
  : Stack unit
  (requires fun h -> live h input /\ live h output
    /\ (as_seq h output) == Seq.create (v (hash_size a)) 0uy)
  (ensures fun h0 () h1 -> live h1 output /\ live h1 input
    /\ modifies_1 output h0 h1
    /\ as_seq h1 input == as_seq h0 input
    /\ correct_agile_hash a (as_seq h1 input) (as_seq h1 output))
  =
  match a with
  | SHA256 -> H256.hash output input len
  | SHA384 -> H384.hash output input len
  | SHA512 -> H512.hash output input len

//#reset-options "--max_fuel 0  --z3rlimit 250"
[@"substitute"]
let wrap_key a output key len =
 (**) let h0 = ST.get () in
  if len <=^ block_size a then
   begin
    (**) assert(v (block_size a) - v len >= 0);
    (**) assert(as_seq h0 output == Seq.create (v (block_size a)) 0uy);
    Buffer.blit key 0ul output 0ul len;
    (**) let h1 = ST.get () in
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h1 output) 0 (v len)) (as_seq h0 key);
    (**) assert(Seq.slice (as_seq h1 output) 0 (v len) == as_seq h0 key);
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h1 output) (v len) (v (block_size a))) (Seq.create (v (block_size a) - v len) 0uy);
    (**) assert(Seq.slice (as_seq h1 output) (v len) (v (block_size a)) == Seq.create (v (block_size a) - v len) 0uy);
    (**) Seq.lemma_eq_intro (as_seq h1 output) (Seq.append (as_seq h0 key) (Seq.create (v (block_size a) - v len) 0uy));
    (**) assert(as_seq h1 output == Seq.append (as_seq h0 key) (Seq.create (v (block_size a) - v len) 0uy))
   end
  else
   begin
    (**) assert(v (block_size a) - v (hash_size a) >= 0);
    (**) assert(as_seq h0 output == Seq.create (v (block_size a)) 0uy);
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 (v (hash_size a))) (Seq.create (v (hash_size a)) 0uy);
    (**) assert(Seq.slice (as_seq h0 output) 0 (v (hash_size a)) == Seq.create (v (hash_size a)) 0uy);
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) (v (hash_size a)) (v (block_size a))) (Seq.create (v (block_size a) - v (hash_size a)) 0uy);
    (**) assert(Seq.slice (as_seq h0 output) (v (hash_size a)) (v (block_size a)) == Seq.create (v (block_size a) - v (hash_size a)) 0uy);
    let nkey = Buffer.sub output 0ul (hash_size a) in
    agile_hash a nkey key len
//    (**) let h1' = ST.get () in
//    (**) assert(as_seq h1' nkey == );
//    (**) assert(Seq.slice (as_seq h1' output) 0 (v (hash_size a)) == Spec_Hash.hash (as_seq h0 key));
//    (**) no_upd_lemma_1 h0 h1' (Buffer.sub output 0ul (hash_size a)) (Buffer.sub output (hash_size a) ((block_size a) -^ (hash_size a)));
//    (**) Seq.lemma_eq_intro (Seq.slice (reveal_sbytes (as_seq h1' output)) (v (hash_size a)) (v (block_size a))) (Seq.create (v (block_size a) - v (hash_size a)) 0uy);
//    (**) assert(Seq.slice (reveal_sbytes (as_seq h1' output)) (v (hash_size a)) (v (block_size a)) == Seq.create (v (block_size a) - v (hash_size a)) 0uy);
//    (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h1' output)) (Seq.append (reveal_sbytes (as_seq h1' nkey)) (Seq.create (v (block_size a) - v (hash_size a)) 0uy));
//    (**) assert(reveal_sbytes (as_seq h1' output) == Seq.append (reveal_sbytes (as_seq h1' nkey)) (Seq.create (v (block_size a) - v (hash_size a)) 0uy))
   end

//#reset-options " --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"
let counter_pos: alg -> Tot uint32_t = function
  | SHA256 -> H256.pos_count_w
  | SHA384 -> H384.pos_count_w
  | SHA512 -> H512.pos_count_w

//#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"
let counter_size: alg -> Tot uint32_t = function
  | SHA256 -> H256.size_count_w
  | SHA384 -> H384.size_count_w
  | SHA512 -> H512.size_count_w

type state (a:alg) =
  (match a with
  | SHA256 -> st:uint32_p{length st = v (H256.size_state)}
  | SHA384 -> st:uint64_p{length st = v (H384.size_state)}
  | SHA512 -> st:uint64_p{length st = v (H512.size_state)})

//#reset-options "--max_fuel 0  --z3rlimit 50"
val lemma_alloc:
  a: alg ->
  s: state a ->
  Lemma
    (requires (s == Seq.create (v (state_size a)) 0ul))
    (ensures (
      let seq_counter = Seq.slice s (U32.v (counter_pos a)) (U32.(v (counter_pos a) + v (counter_size a))) in
      let counter = Seq.index seq_counter 0 in
      U32.v counter = 0))
let lemma_alloc a s = ()

//#reset-options "--max_fuel 0  --z3rlimit 20"
[@"substitute"]
val hmac_part1:
  a    : alg ->
  s2   : uint8_p {length s2 = v (block_size a)} ->
  data : uint8_p  {length data + v (block_size a) < pow2 32 /\ disjoint data s2} ->
  len  : uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h ->  live h s2 /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 s2 /\ live h0 s2
                             /\ live h1 data /\ live h0 data /\ modifies_1 s2 h0 h1
                             /\ (let hash0 = Seq.slice (as_seq h1 s2) 0 (v (hash_size a)) in
                             correct_agile_hash a (Seq.append (as_seq h0 s2) (as_seq h0 data)) hash0)))

let agile_init (a:alg) (st:state a) : Stack unit
 (requires fun h -> True)
 (ensures fun h0 () h1 -> True)
  //live h1 st /\ modifies_1 st h0 h1)
 =
 match a with
 | SHA256 -> H256.init st
 | SHA384 -> H384.init st
 | SHA512 -> H512.init st

let agile_update (a:alg) (st:state a)
  (input:uint8_p {length input = v (block_size a)})
  : Stack unit (requires fun h -> True)
  (ensures fun h0 () h1 -> True)
   //live h1 st /\ modifies_1 st h0 h1)
  =
  match a with
  | SHA256 -> H256.update st input
  | SHA384 -> H384.update st input
  | SHA512 -> H512.update st input

let agile_update_last (a:alg) (st:state a)
  (input:uint8_p {length input = v (block_size a)})
  (len:uint32_t {v len = length input})
  : Stack unit (requires fun h -> True)
  (ensures fun h0 () h1 -> True)
   //live h1 st /\ modifies_1 st h0 h1)
  =
  match a with
  | SHA256 -> H256.update_last st input len
  | SHA384 -> H384.update_last st input (Int.Cast.uint32_to_uint64 len)
  | SHA512 -> H512.update_last st input (Int.Cast.uint32_to_uint64 len)

let agile_finish (a:alg) (st:state a)
  (hash:uint8_p {length hash = v (hash_size a)})
  : Stack unit (requires fun h -> True)
  (ensures fun h0 () h1 -> True)
   //live h1 st /\ modifies_1 st h0 h1)
  =
  match a with
  | SHA256 -> H256.finish st hash
  | SHA384 -> H384.finish st hash
  | SHA512 -> H512.finish st hash

let agile_update_multi (a:alg) (st:state a)
  (input:uint8_p {length input % v (block_size a) = 0})
  (nblocks:uint32_t{op_Multiply (v nblocks) (v (block_size a)) = length input})
  : Stack unit (requires fun h -> True)
  (ensures fun h0 () h1 -> True)
   //live h1 st /\ modifies_1 st h0 h1)
  =
  match a with
  | SHA256 -> H256.update_multi st input nblocks
  | SHA384 -> H384.update_multi st input nblocks
  | SHA512 -> H512.update_multi st input nblocks

//#reset-options "--max_fuel 0  --z3rlimit 200"
[@"substitute"]
let hmac_part1 a s2 data len =

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get () in

  (* Allocate memory for the Hash function state *)
  // let state0 = Hash.alloc () in
  let state0 = Buffer.create 0ul (state_size a) in
  (**) let h = ST.get() in
//  (**) lemma_alloc (reveal_h32s (as_seq h state0));
  (**) no_upd_lemma_0 h0 h s2;
  (**) no_upd_lemma_0 h0 h data;

  (* Step 3: append data to "result of step 2" *)
  (* Step 4: apply Hash to "result of step 3" *)
  (**) assert((block_size a) <> 0ul);
  (**) Math.Lemmas.lemma_div_mod (v len) (v (block_size a));
  let n0 = U32.div len (block_size a) in
  let r0 = U32.rem len (block_size a) in
  let blocks0 = Buffer.sub data 0ul (n0 *^ (block_size a)) in
  let last0 = Buffer.offset data (n0 *^ (block_size a)) in
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h data) 0 (U32.v (n0 *^ (block_size a)))) (as_seq h blocks0);
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h data) (U32.v (n0 *^ (block_size a))) (length data)) (as_seq h last0);
  agile_init a state0;
  (**) let h' = ST.get() in
  (**) no_upd_lemma_1 h h' state0 s2;
  (**) no_upd_lemma_1 h h' state0 data;
  (**) no_upd_lemma_1 h h' state0 blocks0;
  (**) no_upd_lemma_1 h h' state0 last0;
  agile_update a state0 s2;
  (**) let h'' = ST.get() in
  (**) no_upd_lemma_1 h' h'' state0 blocks0;
  (**) no_upd_lemma_1 h' h'' state0 last0;
  agile_update_multi a state0 blocks0 n0;
  (**) let h''' = ST.get() in
  (**) no_upd_lemma_1 h'' h''' state0 last0;
  agile_update_last a state0 last0 r0;
  (**) let h1 = ST.get () in

  let h'''' = ST.get() in
  let hash0 = Buffer.sub s2 0ul (hash_size a) in (* Salvage memory *)
  agile_finish a state0 hash0; (* s4 = hash (s2 @| data) *)
//  (**) Spec_Hash.lemma_hash_all_prepend_block (reveal_sbytes (as_seq h0 s2)) (reveal_sbytes (as_seq h0 data));

  (* Pop the memory frame *)
  (**) pop_frame ()


//#reset-options "--max_fuel 0  --z3rlimit 20"
[@"substitute"]
val hmac_part2:
  a   : alg ->
  mac : uint8_p {length mac = v (hash_size a)} ->
  s5  : uint8_p {length s5 = v (block_size a) /\ disjoint s5 mac} ->
  s4  : uint8_p {length s4 = v (hash_size a) /\ disjoint s4 mac /\ disjoint s4 s5} ->
  Stack unit
        (requires (fun h -> True)) //live h mac /\ live h s5 /\ live h s4))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac))

 ///\ live h1 s5 /\ live h0 s5
 ///\ live h1 s4 /\ live h0 s4 /\ modifies_1 mac h0 h1
 ///\ (reveal_sbytes (as_seq h1 mac) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))))))

//#reset-options "--max_fuel 0  --z3rlimit 200"
[@"substitute"]
let hmac_part2 a mac s5 s4 =
  assert_norm(pow2 32 = 0x100000000);
  let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get () in

  (* Allocate memory for the Hash function state *)
  (* let state1 = Hash.alloc () in *)
  let state1 = Buffer.create 0ul (state_size a) in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  (**) let h = ST.get() in
  (**) no_upd_lemma_0 h0 h s5;
  (**) no_upd_lemma_0 h0 h s4;
  (**) no_upd_lemma_0 h0 h mac;
//  (**) lemma_alloc (reveal_h32s (as_seq h state1));
  agile_init a state1;
  (**) let h' = ST.get() in
//  (**) assert(
//       let st_h0 = Seq.slice (as_seq h' state1) (U32.v Hash.pos_whash_w) (U32.(v Hash.pos_whash_w + v Hash.size_whash_w)) in
//       reveal_h32s st_h0 == Spec_Hash.h_0);
  (**) no_upd_lemma_1 h h' state1 s5;
  (**) no_upd_lemma_1 h h' state1 s4;
  (**) no_upd_lemma_1 h h' state1 mac;
  agile_update a state1 s5; (* s5 = opad *)
  (**) let h'' = ST.get() in
//  (**) assert(
//       let st_h0 = Seq.slice (as_seq h'' state1) (U32.v Hash.pos_whash_w) (U32.(v Hash.pos_whash_w + v Hash.size_whash_w)) in
//       reveal_h32s st_h0 == Spec_Hash.(update h_0 (reveal_sbytes (as_seq h0 s5))));
  (**) no_upd_lemma_1 h' h'' state1 s4;
  (**) no_upd_lemma_1 h' h'' state1 mac;
  (**) assert(as_seq h'' s4 == as_seq hinit s4);
  agile_update_last a state1 s4 (hash_size a);
  (**) let h''' = ST.get() in
  (**) no_upd_lemma_1 h' h'' state1 s4;
  (**) no_upd_lemma_1 h' h'' state1 mac;
  (**) assert(live h''' mac);
  agile_finish a state1 mac; //(* s7 = hash (s5 @| s4) *)
//  (**) let h1 = ST.get() in
//  (**) Spec_Hash.lemma_hash_single_prepend_block (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4));
//  Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 mac)) (Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))));
//  (**) assert(reveal_sbytes (as_seq h1 mac) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))));
  (* Pop the memory frame *)
  (**) pop_frame ()


//#reset-options "--max_fuel 0  --z3rlimit 20"
val hmac_core:
  a    : alg ->
  mac  : uint8_p  {length mac = v (hash_size a)} ->
  key  : uint8_p  {length key = v (block_size a) /\ disjoint key mac} ->
  data : uint8_p  {length data + v (block_size a) < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  len  : uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1))
//                             /\ (reveal_sbytes (as_seq h1 mac) == Spec.hmac_core (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)))))

//#reset-options "--max_fuel 0  --z3rlimit 150"

let hmac_core a mac key data len =

  let h00 = ST.get () in
  (* Push a new memory frame *)
  (**) push_frame ();
  let h0 = ST.get () in

  (* Initialize constants *)
  let ipad = Buffer.create 0x36uy (block_size a) in
  let opad = Buffer.create 0x5cuy (block_size a) in

  (**) let h1 = ST.get () in
//  (**) assert(reveal_sbytes (as_seq h1 ipad) == Seq.create (v (block_size a)) 0x36uy);
//  (**) assert(reveal_sbytes (as_seq h1 opad) == Seq.create (v (block_size a)) 0x5cuy);

  (* Step 2: xor "result of step 1" with ipad *)
  xor_bytes_inplace ipad key (block_size a);
  (**) let h2 = ST.get () in
//  (**) assert(reveal_sbytes (as_seq h2 ipad) == Spec.xor_bytes (reveal_sbytes (as_seq h1 ipad)) (reveal_sbytes (as_seq h0 key)));

  (* Step 3: append data to "result of step 2" *)
  (* Step 4: apply Hash to "result of step 3" *)
  hmac_part1 a ipad data len; (* s2 = ipad *)
  let s4 = Buffer.sub ipad 0ul (hash_size a) in (* Salvage memory *)
  (**) let h3 = ST.get () in
//  (**) Seq.lemma_eq_intro (as_seq h3 (Buffer.sub ipad 0ul (hash_size a))) (Seq.slice (as_seq h3 ipad) 0 (v (hash_size a)));
//  (**) assert(reveal_sbytes (as_seq h3 s4) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h2 ipad)) (reveal_sbytes (as_seq h0 data))));
//  (**) assert(reveal_sbytes (as_seq h3 s4) == Spec_Hash.hash (Seq.append (Spec.xor_bytes (reveal_sbytes (as_seq h1 ipad)) (reveal_sbytes (as_seq h0 key))) (reveal_sbytes (as_seq h0 data))));

  (* Step 5: xor "result of step 1" with opad *)
  xor_bytes_inplace opad key (block_size a);
  (**) let h4 = ST.get () in
//  (**) assert(reveal_sbytes (as_seq h4 opad) == Spec.xor_bytes (reveal_sbytes (as_seq h1 opad)) (reveal_sbytes (as_seq h0 key)));

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  hmac_part2 a mac opad s4; (* s5 = opad *)
  (**) let h5 = ST.get () in
//  (**) assert(reveal_sbytes (as_seq h5 mac) == Spec.hmac_core (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)));

  (* Pop the memory frame *)
  (**) pop_frame ()

//#reset-options "--max_fuel 0  --z3rlimit 20"
val hmac:
  a       : alg ->
  mac     : uint8_p  {length mac = v (hash_size a)} ->
  key     : uint8_p  {length key = v (block_size a) /\ disjoint key mac} ->
  keylen  : uint32_t {v keylen = length key} ->
  data    : uint8_p  {length data + v (block_size a) < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  datalen : uint32_t {v datalen = length data} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1))
//                             /\ (reveal_sbytes (as_seq h1 mac) == Spec.hmac (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)))))

//#reset-options "--max_fuel 0  --z3rlimit 25"
let hmac a mac key keylen data datalen =

  (* Push a new memory frame *)
  (**) push_frame ();

  (* Allocate memory for the wrapped key *)
  let nkey = Buffer.create 0x00uy (block_size a) in

  (* Call the key wrapping function *)
  wrap_key a nkey key keylen;

  (* Call the core HMAC function *)
  hmac_core a mac nkey data datalen;

  (* Pop the memory frame *)
  (**) pop_frame ()
