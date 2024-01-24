module Hacl.Streaming.Blake2.Params

open Lib.IntTypes
open Lib.Buffer

let params a =
  B.pointer (Core.blake2_params a)

let footprint #a h s =
  B.(loc_union (loc_addr_of_buffer s) (Core.blake2_params_loc (B.deref h s)))

let freeable_s (#a: Spec.alg) (p: Core.blake2_params a) =
  match a with
  | Spec.Blake2S -> freeable (Core.Mkblake2s_params?.salt p) /\ freeable (Core.Mkblake2s_params?.personal p)
  | Spec.Blake2B -> freeable (p.Core.salt) /\ freeable (p.Core.personal)

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

let alloca a = match a with
  | Spec.Blake2S ->
      let salt = create 8ul (u8 0) in
      let personal = create 8ul (u8 0) in
      let p = {
        digest_length = u8 32;
        key_length = u8 0;
        fanout = u8 1;
        depth = u8 1;
        leaf_length = u32 0;
        node_offset = u32 0;
        xof_length = u16 0;
        node_depth = u8 0;
        inner_length = u8 0;
        salt; personal } <: Core.blake2s_params
     in B.alloca p 1ul

  | Spec.Blake2B ->
      let salt = create 16ul (u8 0) in
      let personal = create 16ul (u8 0) in
      let p = {
        digest_length = u8 64;
        key_length = u8 0;
        fanout = u8 1;
        depth = u8 1;
        leaf_length = u32 0;
        node_offset = u32 0;
        xof_length = u32 0;
        node_depth = u8 0;
        inner_length = u8 0;
        salt; personal } <: Core.blake2b_params
     in B.alloca p 1ul

#push-options "--z3rlimit 20"
let create_in a r = match a with
  | Spec.Blake2S ->
      let salt: buffer uint8 = B.malloc r (u8 0) 8ul in
      let personal: buffer uint8 = B.malloc r (u8 0) 8ul in
      let p = {
        digest_length = u8 32;
        key_length = u8 0;
        fanout = u8 1;
        depth = u8 1;
        leaf_length = u32 0;
        node_offset = u32 0;
        xof_length = u16 0;
        node_depth = u8 0;
        inner_length = u8 0;
        salt; personal } <: Core.blake2s_params
     in B.malloc r p 1ul

  | Spec.Blake2B ->
      let salt: buffer uint8 = B.malloc r (u8 0) 16ul in
      let personal: buffer uint8 = B.malloc r (u8 0) 16ul in
      let p = {
        digest_length = u8 32;
        key_length = u8 0;
        fanout = u8 1;
        depth = u8 1;
        leaf_length = u32 0;
        node_offset = u32 0;
        xof_length = u32 0;
        node_depth = u8 0;
        inner_length = u8 0;
        salt; personal } <: Core.blake2b_params
     in B.malloc r p 1ul

let free #a s =
  let p = B.index s 0ul in
  B.free (Core.get_salt p <: B.buffer uint8);
  B.free (Core.get_personal p <: B.buffer uint8);
  B.free s

let copy #a s_src s_dst =
  let p_src = B.index s_src 0ul in
  let p_dst = B.index s_dst 0ul in
  B.blit (Core.get_salt p_src <: B.buffer uint8) 0ul
         (Core.get_salt p_dst <: B.buffer uint8) 0ul
         (Core.salt_len a);
  B.blit (Core.get_personal p_src <: B.buffer uint8) 0ul
         (Core.get_personal p_dst <: B.buffer uint8) 0ul
         (Core.personal_len a);

  let p' = Core.set_personal (Core.set_salt p_src (Core.get_salt p_dst)) (Core.get_personal p_dst) in
  B.upd s_dst 0ul p'
