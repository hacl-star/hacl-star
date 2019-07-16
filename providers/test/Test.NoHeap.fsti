module Test.NoHeap

module H = EverCrypt.Hash
module B = LowStar.Buffer
module L = Test.Lowstarize

open FStar.HyperStack.ST

let vec8 = L.lbuffer UInt8.t

inline_for_extraction noextract
let test_many #a (label: C.String.t)
  (f: a -> Stack unit (fun _ -> True) (fun _ _ _ -> True)) (vec: L.lbuffer a):
  Stack unit (fun _ -> True) (fun _ _ _ -> True)
=
  C.String.print label;
  C.String.(print !$"\n");
  let L.LB len vs = vec in
  let f (i:UInt32.t{FStar.UInt32.(0 <= v i /\ v i < v len)}): Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)
  =
    let open LowStar.BufferOps in
    B.recall vs;
    f vs.(i)
  in
  C.Loops.for 0ul len (fun _ _ -> True) f

let hash_vector = H.alg & C.String.t & vec8 & UInt32.t
val test_hash: vs:L.lbuffer hash_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

let hmac_vector = H.alg & vec8 & vec8 & vec8
val test_hmac: vs:L.lbuffer hmac_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

let hkdf_vector = H.alg & vec8 & vec8 & vec8 & vec8 & vec8
val test_hkdf: vs:L.lbuffer hkdf_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

let chacha20_vector = vec8 & vec8 & UInt32.t & vec8 & vec8
val test_chacha20: L.lbuffer chacha20_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

val test_poly1305 (_: unit) : Stack unit (fun _ -> True) (fun _ _ _ -> True)

val test_curve25519 (_: unit) : Stack unit (fun _ -> True) (fun _ _ _ -> True)

val test_chacha20poly1305 (_: unit) : Stack unit (fun _ -> True) (fun _ _ _ -> True)

val main: unit -> Stack Int32.t (fun _ -> True) (fun _ _ _ -> True)
