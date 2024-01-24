module Hacl.Streaming.Blake2.Params

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

let alloca a = admit()
let create_in a r = admit()
let free #a s = admit ()
let copy #a s_src s_dst = admit()
