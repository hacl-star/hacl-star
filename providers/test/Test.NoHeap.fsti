module Test.NoHeap

module H = EverCrypt.Hash
module B = LowStar.Buffer
module L = Test.Lowstarize

open FStar.HyperStack.ST

let vec8 = L.lbuffer UInt8.t

let hash_vector = H.alg & C.String.t & vec8 & UInt32.t
val test_hash: vs:L.lbuffer hash_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

let hmac_vector = H.alg & vec8 & vec8 & vec8
val test_hmac: vs:L.lbuffer hmac_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

let hkdf_vector = H.alg & vec8 & vec8 & vec8 & vec8 & vec8
val test_hkdf: vs:L.lbuffer hkdf_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

let chacha20_vector = vec8 & vec8 & UInt32.t & vec8 & vec8
val test_chacha20: L.lbuffer chacha20_vector -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

val main: unit -> Stack Int32.t (fun _ -> True) (fun _ _ _ -> True)
