module Hacl.Impl.HKDF_SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

module SpecSHA2 = Spec.SHA2
module SpecHash = Spec.Hash
module SpecHMAC = Spec.HMAC

module Hash = Hacl.Impl.SHA2_256
module HMAC = Hacl.Impl.HMAC_SHA2_256


inline_for_extraction noextract
let a = Spec.SHA2.SHA2_256



val hkdf_extract:
    output: lbuffer uint8 (size (Spec.SHA2.size_hash a))
  -> salt: buffer uint8 {length salt <= Spec.SHA2.max_input a}
  -> slen: size_t{v slen == length salt}
  -> ikm: buffer uint8
  -> ilen: size_t{ v ilen == length ikm
                /\ length salt + length ikm + Spec.SHA2.size_block a <= Spec.SHA2.max_input a
                /\ Spec.SHA2.size_hash a + length ikm + Spec.SHA2.size_block a <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h salt /\ live h ikm
                 /\ disjoint output salt /\ disjoint output ikm))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_extract output salt slen ikm ilen =
  push_frame ();
  admit();
  let salt0 = create (size (Spec.SHA2.size_hash a)) (u8 0) in
  (if slen = size 0 then
    HMAC.hmac output salt0 (size (Spec.SHA2.size_hash a)) ikm ilen
  else
    HMAC.hmac output salt slen ikm ilen);
  pop_frame()


#reset-options "--z3rlimit 25"

val hkdf_round0:
    output: lbuffer uint8 (size (Spec.SHA2.size_hash a))
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk <= Spec.SHA2.max_input a}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.SHA2.size_hash a + 1 <= max_size_t
                /\ length prk + length info + 1 + Spec.SHA2.size_hash a + Spec.SHA2.size_block a <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info
                 /\ disjoint output prk /\ disjoint output info))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_round0 output prk plen info ilen =
  push_frame ();
  let input = create (ilen +. 1ul) (u8 0) in
  update_sub #MUT #uint8 #(ilen +. 1ul) input (size 0) ilen info;
  upd input ilen (u8 1);
  HMAC.hmac output prk plen input (ilen +. 1ul);
  pop_frame ()


val hkdf_round:
    output: lbuffer uint8 (size (Spec.SHA2.size_hash a))
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk <= Spec.SHA2.max_input a}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.SHA2.size_hash a + 1 <= max_size_t
                /\ length prk + length info + 1 + Spec.SHA2.size_hash a + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> i:size_t{1 < v i /\ v i <= 255}
  -> ti: lbuffer uint8 (size (Spec.SHA2.size_hash a)) ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info /\ live h ti
                 /\ disjoint output prk /\ disjoint output info /\ disjoint output ti))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_round output prk plen info ilen i ti =
  push_frame ();
  let input = create (size (Spec.SHA2.size_hash a) +. ilen +. 1ul) (u8 0) in
  update_sub input 0ul (size (Spec.SHA2.size_hash a)) ti;
  update_sub #MUT #uint8 #(size (Spec.SHA2.size_hash a) +. ilen +. 1ul) input (size (Spec.SHA2.size_hash a)) ilen info;
  upd #uint8 #(size (Spec.SHA2.size_hash a) +. ilen +. 1ul) input (size (Spec.SHA2.size_hash a) +. ilen) (to_u8 (size_to_uint32 i));
  HMAC.hmac output prk plen input (size (Spec.SHA2.size_hash a) +. ilen +. 1ul);
  pop_frame ()


#reset-options "--z3rlimit 500"

val hkdf_expand:
    output: buffer uint8
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk <= Spec.SHA2.max_input a}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.SHA2.size_hash a + 1 <= max_size_t
                /\ length prk + length info + 1 + Spec.SHA2.size_hash a + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> len: size_t{ v len == length output
               /\ v len + Spec.SHA2.size_hash a <= max_size_t
               /\ v len / (Spec.SHA2.size_hash a) + 2 <= 255} ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info
                 /\ disjoint output prk /\ disjoint output info))
  (ensures  (fun h0 _ h1 -> modifies1 #uint8 #len output h0 h1))

let hkdf_expand output prk plen info ilen len =
  push_frame ();
  let n : size_t = len /. (size (Spec.SHA2.size_hash a)) +. 1ul in
  let t = create (n *. size (Spec.SHA2.size_hash a)) (u8 0) in
  let t0 = sub t (size 0) (size (Spec.SHA2.size_hash a)) in
  (* Compute T(0) *)
  hkdf_round0 t0 prk plen info ilen;
  (* Compute T(1) ... T(N)*)
  assert(v n - 1 + 2 <= 255);
  let h0 = ST.get () in
  loop_range_nospec #h0 (size 2) (n -. 1ul) t
    (fun i ->
       let ti0 = sub t ((i -. 2ul) *. size (Spec.SHA2.size_hash a)) (size (Spec.SHA2.size_hash a)) in
       let ti1 = sub t ((i -. 1ul) *. size (Spec.SHA2.size_hash a)) (size (Spec.SHA2.size_hash a)) in
       hkdf_round ti1 prk plen info ilen i ti0
    );
  let res = sub t (size 0) len in
  copy output res;
  pop_frame ()
