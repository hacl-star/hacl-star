module MerkleTree.EverCrypt

module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer

module HST = FStar.HyperStack.ST
module MTH = MerkleTree.New.High
module MTLH = MerkleTree.Low.Hashfunctions
module MTLD = MerkleTree.Low.Datastructures

open LowStar.Regional

let hash #hash_size = MTLD.hash #hash_size
let mt_p = MerkleTree.Low.mt_p
let mt_loc = MerkleTree.Low.mt_loc
let mt_safe = MerkleTree.Low.mt_safe
let mt_lift = MerkleTree.Low.mt_lift

[@ (Comment "  Default hash function")]
val mt_sha256_compress: MTLH.hash_fun_t #32ul #(Ghost.hide MTH.sha256_compress)

[@ (Comment "  Construction wired to sha256 from EverCrypt

  @param[in]  init   The initial hash") "c_inline"]
val mt_create: r:HST.erid -> init:hash #32ul -> HST.ST mt_p
   (requires (fun h0 ->
     Rgl?.r_inv (MTLD.hreg 32ul) h0 init /\
     HH.disjoint r (B.frameOf init)))
   (ensures (fun h0 mt h1 ->
     // memory safety
     B.modifies B.(loc_union (mt_loc mt) (B.loc_all_regions_from false (B.frameOf init))) h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     MerkleTree.Low.MT?.hash_size (B.get h1 mt 0) = 32ul /\
     mt_lift h1 mt == MTH.mt_create 32 MTH.sha256_compress (Rgl?.r_repr (MTLD.hreg 32ul) h0 init)))

