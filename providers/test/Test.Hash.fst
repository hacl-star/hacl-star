module Test.Hash

module H = EverCrypt.Hash

module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module MP = LowStar.ModifiesPat

open LowStar.BufferOps
open Spec.Hash.Helpers

open ST

let main (): St unit =
  push_frame ();
  let s1 = H.alloca SHA2_256 in
  let h1 = ST.get () in
  let s2 = H.alloca SHA2_384 in
  let h2 = ST.get () in
  H.frame_invariant M.loc_none s1 h1 h2;
  H.init #(Ghost.hide SHA2_256) s1;
  let h3 = ST.get () in
  H.frame_invariant (H.footprint s1 h1) s2 h2 h3;
  H.init #(Ghost.hide SHA2_384) s2;
  pop_frame ()
