module Hacl.Streaming.Blake2.Params

open Lib.IntTypes
open Lib.Buffer
open LowStar.BufferOps

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST

let _align = ()

// MUST BE A SEPARATE TYPE ABBREVIATION
// nothing works if inlined underneath B.pointer, below
let blake2_params a (i: index a) =
  x:Core.blake2_params a {
      x.digest_length == i.digest_length /\
      x.key_length == i.key_length
    }

let params (a: Spec.alg) (i: index a) =
  B.pointer (blake2_params a i)

let footprint #a h s =
  B.(loc_union (loc_addr_of_buffer s) (Core.blake2_params_loc (B.deref h s)))

let freeable_s (#a: Spec.alg) (p: Core.blake2_params a) : GTot prop =
  freeable (p.Core.salt) /\ freeable (p.Core.personal)

let freeable #a h s =
  B.freeable s /\ freeable_s (B.deref h s)

let invariant #a #i h s =
  B.live h s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (Core.blake2_params_loc (B.deref h s))) /\
  Core.blake2_params_inv h (B.deref h s)

let v #a h s =
  let p = B.deref h s in
  Core.blake2_params_v h p

let invariant_loc_in_footprint #a h s = ()
let frame_invariant #a l s h0 h1 = ()
let frame_freeable #a l s h0 h1 = ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let get_params #a #i s =
  B.index s 0ul

let alloca a i =
  let open Core in
  let salt = create (salt_len a) (u8 0) in
  let personal = create (personal_len a) (u8 0) in
  let _ = allow_inversion Spec.Blake2.alg in
  let p = {
    digest_length = i.digest_length;
    key_length = i.key_length;
    fanout = u8 1;
    depth = u8 1;
    leaf_length = u32 0;
    node_offset = u64 0;
    node_depth = u8 0;
    inner_length = u8 0;
    salt; personal }
 in B.alloca p 1ul

#push-options "--z3rlimit 20"
let create_in a i r =
  let open Core in
  let open Hacl.Streaming.Interface in
  let h0 = ST.get () in
  let salt: buffer uint8 = fallible_malloc r (u8 0) (salt_len a) in
  if B.is_null salt then
    None
  else
    let personal: buffer uint8 = fallible_malloc r (u8 0) (personal_len a) in
    if B.is_null personal then (
      B.free salt;
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      None
    ) else
      let p = {
        digest_length = i.digest_length;
        key_length = i.key_length;
        fanout = u8 1;
        depth = u8 1;
        leaf_length = u32 0;
        node_offset = u64 0;
        node_depth = u8 0;
        inner_length = u8 0;
        salt; personal }
      in
      let r = fallible_malloc r p 1ul in
      if B.is_null r then (
        B.free salt;
        B.free personal;
        let h1 = ST.get () in
        B.(modifies_only_not_unused_in loc_none h0 h1);
        None
      ) else
        Some r

let free #a s =
  let p = B.index s 0ul in
  B.free (p.salt <: B.buffer uint8);
  B.free (p.personal <: B.buffer uint8);
  B.free s

let copy #a s_src s_dst =
  let p_src = B.index s_src 0ul in
  let p_dst = B.index s_dst 0ul in
  B.blit (p_src.salt <: B.buffer uint8) 0ul
         (p_dst.salt <: B.buffer uint8) 0ul
         (Core.salt_len a);
  B.blit (p_src.personal <: B.buffer uint8) 0ul
         (p_dst.personal <: B.buffer uint8) 0ul
         (Core.personal_len a);

  let p' = {p_src with salt = p_dst.salt; personal = p_dst.personal} in
  B.upd s_dst 0ul p'
