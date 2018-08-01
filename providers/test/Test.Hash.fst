module Test.Hash

module H = EverCrypt.Hash

module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module MP = LowStar.ModifiesPat

open LowStar.BufferOps

open ST

let main (): St unit =
  let s1 = H.create H.SHA256 in
  let h1 = ST.get () in
  let s2 = H.create H.SHA384 in
  let h2 = ST.get () in
  H.frame_invariant M.loc_none s1 h1 h2;
  H.init s1;
  let h3 = ST.get () in
  H.frame_invariant (H.footprint s1 h1) s2 h2 h3;
  H.init s2
