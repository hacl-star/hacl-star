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
    output: buffer uint8{length output == Spec.SHA2.size_hash a}
  -> salt: buffer uint8 {length salt <= Spec.SHA2.max_input a}
  -> slen: size_t{v slen == length salt}
  -> ikm: buffer uint8
  -> ilen: size_t{ v ilen == length ikm
                /\ length salt + length ikm + Spec.SHA2.size_block a <= Spec.SHA2.max_input a
                /\ Spec.SHA2.size_hash a + length ikm + Spec.SHA2.size_block a <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h salt /\ live h ikm
                 /\ disjoint output salt /\ disjoint output ikm))
  (ensures  (fun h0 _ h1 -> modifies1 #uint8 #(Spec.SHA2.size_hash a) output h0 h1))

let hkdf_extract output salt slen ikm ilen =
  let salt0 = create #uint8 #(Spec.SHA2.size_hash a) (size (Spec.SHA2.size_hash a)) (u8 0) in
  if slen = 0ul then
    HMAC.hmac output salt0 (size (Spec.SHA2.size_hash a)) ikm ilen
  else
    HMAC.hmac output salt (size (Spec.SHA2.size_hash a)) ikm ilen


val hkdf_round0:
    output: lbuffer uint8 (Spec.SHA2.size_hash a)
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
  let input = create (ilen +. 1ul) (u8 0) in
  update_sub input (size 0) ilen info;
  upd #uint8 #(v ilen + 1) input ilen (u8 1);
  HMAC.hmac output prk plen input (ilen +. 1ul)




val hkdf_round:
    output: lbuffer uint8 (Spec.SHA2.size_hash a)
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk <= Spec.SHA2.max_input a}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.SHA2.size_hash a + 1 <= max_size_t
                /\ length prk + length info + 1 + Spec.SHA2.size_hash a + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> i:nat{1 < i /\ i <= 255}
  -> ti: lbuffer uint8 (Spec.SHA2.size_hash a) ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info
                 /\ disjoint output prk /\ disjoint output info))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_round output prk plen info ilen i ti =
  let input = create (size (Spec.SHA2.size_hash a) +. ilen +. 1ul) (u8 0) in
  update_sub input 0ul (size (Spec.SHA2.size_hash a)) ti;
  update_sub input (size (Spec.SHA2.size_hash a)) ilen info;
  upd #uint8 #(Spec.SHA2.size_hash a + v ilen + 1) input (size (Spec.SHA2.size_hash a) +. ilen) (u8 i);
  HMAC.hmac output prk plen input ilen



val hkdf_expand:
    output: buffer uint8
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk <= Spec.SHA2.max_input a}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.SHA2.size_hash a + 1 <= max_size_t
                /\ length prk + length info + 1 + Spec.SHA2.size_hash a + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> len: size_t{v len == length output} ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info
                 /\ disjoint output prk /\ disjoint output info))
  (ensures  (fun h0 _ h1 -> modifies1 #uint8 #(v len) output h0 h1))

let hkdf_expand output prk plen info ilen len =
  let n : size_t = len /. (size (Spec.SHA2.size_hash a)) + 1 in
  let t0 = create #uint8 (size (Spec.SHA2.size_hash a)) (u8 0) in
  let t = create #uint8 (n *. size (Spec.SHA2.size_hash a)) (u8 0) in
  (* Compute T(0) *)
  hkdf_round0 t0 prk plen info ilen;
  update_sub t (size 0) (Spec.SHA2.size_hash a) t0;
  (* Compute T(1) ... T(N)*)
  let h0 = ST.get () in
  loop_range_nospec #h0 (size 2) (n +. 1ul) t
    (fun i ->
       let ti = sub t ((i -. 2ul) *. size (Spec.SHA2.size_hash a)) (size (Spec.SHA2.size_hash a)) in
       let ti1 = sub t ((i -. 1ul) *. size (Spec.SHA2.size_hash a)) (size (Spec.SHA2.size_hash a)) in
       hkdf_round ti1 prk plen info ilen i ti
    );
  let res = sub #uint8 #(v n * (Spec.SHA2.size_hash a)) t (size 0) len in
  copy #uint8 #(v len) output len res
