module MerkleTree.Bug

open FStar.Integers

module V = LowStar.Vector
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

type hash_size_t = n:V.uint32_t{n > 0ul}
type hash (#hsz:hash_size_t) = b:B.buffer FStar.UInt8.t { B.len b = hsz \/ B.g_is_null b }

let f (#hsz:hash_size_t) (h:hash #hsz)
: HST.ST (V.vector (hash #hsz))
    (requires (fun h0 -> True))
    (ensures (fun h0 v h1 -> True))
= let v = V.alloc_empty hash in
  let h0 = HST.get() in
  assert (V.live h0 v);
  assume (V.freeable v);
  assert (not (V.is_full v));
  assume (HST.is_eternal_region (V.frameOf v));
  assert (V.Vec?.sz v == 0ul);
  assert (V.Vec?.cap v == 0ul);
  V.insert v h
