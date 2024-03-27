module Hacl.Streaming.Blake2.Params

open Lib.IntTypes
open Lib.Buffer

module B = LowStar.Buffer

let params a =
  B.pointer (Core.blake2_params a)

let footprint #a h s =
  B.(loc_union (loc_addr_of_buffer s) (Core.blake2_params_loc (B.deref h s)))

let freeable_s (#a: Spec.alg) (p: Core.blake2_params a) : GTot prop =
  freeable (p.Core.salt) /\ freeable (p.Core.personal)

let freeable #a h s =
  B.freeable s /\ freeable_s (B.deref h s)

let invariant #a h s =
  B.live h s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (Core.blake2_params_loc (B.deref h s))) /\
  Core.blake2_params_inv h (B.deref h s)

let v #a h s =
  let p = B.deref h s in
  Core.blake2_params_v h p

let invariant_loc_in_footprint #a h s = ()
let frame_invariant #a l s h0 h1 = ()
let frame_freeable #a l s h0 h1 = ()

let get_params #a s = B.index s 0ul

let alloca a =
  let open Core in
  let salt = create (salt_len a) (u8 0) in
  let personal = create (personal_len a) (u8 0) in
  let p = {
    digest_length = u8 32;
    key_length = u8 0;
    fanout = u8 1;
    depth = u8 1;
    leaf_length = u32 0;
    node_offset = u64 0;
    node_depth = u8 0;
    inner_length = u8 0;
    salt; personal }
 in B.alloca p 1ul

#push-options "--z3rlimit 20"
let create_in a r =
  let open Core in
  let salt: buffer uint8 = B.malloc r (u8 0) (salt_len a) in
  let personal: buffer uint8 = B.malloc r (u8 0) (personal_len a) in
  let p = {
    digest_length = u8 32;
    key_length = u8 0;
    fanout = u8 1;
    depth = u8 1;
    leaf_length = u32 0;
    node_offset = u64 0;
    node_depth = u8 0;
    inner_length = u8 0;
    salt; personal }
  in B.malloc r p 1ul

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
