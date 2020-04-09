module Hacl.Spec.SHA2.Vec

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.IntVector
module NTup = Lib.NTuple
open Spec.Hash.Definitions
module Constants = Spec.SHA2.Constants
module Spec = Spec.SHA2
friend Spec.SHA2
friend Spec.SHA2.Lemmas

type m_spec =
  | M32
  | M128
  | M256
  | M512

let lanes_t = n:nat{n == 1 \/ n == 2 \/ n == 4 \/ n == 8 \/ n == 16}
inline_for_extraction let lanes (a:sha2_alg) (m:m_spec) : lanes_t =
  match a,m with
  | SHA2_224,M128
  | SHA2_256,M128 -> 4
  | SHA2_224,M256
  | SHA2_256,M256 -> 8
  | SHA2_224,M512
  | SHA2_256,M512 -> 16
  | SHA2_384,M128
  | SHA2_512,M128 -> 2
  | SHA2_384,M256
  | SHA2_512,M256 -> 4
  | SHA2_384,M512
  | SHA2_512,M512 -> 8
  | _ -> 1

inline_for_extraction
let element_t (a:sha2_alg) (m:m_spec) = vec_t (word_t a) (lanes a m)
inline_for_extraction
val zero_element: a:sha2_alg -> m:m_spec -> element_t a m
let zero_element a m = vec_zero (word_t a) (lanes a m) 

inline_for_extraction
val load_element: a:sha2_alg -> m:m_spec -> word a -> element_t a m
let load_element a m x = vec_load x (lanes a m) 

inline_for_extraction
let ( +| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> element_t a m -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( +| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( +| ) #U64 #(lanes a m)

inline_for_extraction
let ( ^| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> element_t a m -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( ^| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( ^| ) #U64 #(lanes a m)

inline_for_extraction
let ( &| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> element_t a m -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( &| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( &| ) #U64 #(lanes a m)

inline_for_extraction
let ( ~| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( ~| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( ~| ) #U64 #(lanes a m)

inline_for_extraction
let ( >>>| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> rotval (word_t a) -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( >>>| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( >>>| ) #U64 #(lanes a m)

inline_for_extraction
let ( >>| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> shiftval (word_t a) -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( >>| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( >>| ) #U64 #(lanes a m)

inline_for_extraction
val _Ch: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m -> element_t a m -> element_t a m
let _Ch #a #m x y z = (x &| y) ^| (~| x &| z) //TODO: Ch(e,f,g)=((f^g)&e)^g

inline_for_extraction
val _Maj: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m -> element_t a m -> element_t a m
let _Maj #a #m x y z = (x &| y) ^| ((x &| z) ^| (y &| z)) // TODO: Maj(a,b,c) = Ch(a^b,c,b)

inline_for_extraction
val _Sigma0: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
inline_for_extraction
let _Sigma0 #a #m x = Spec.((x >>>| (op0 a).c0) ^| (x >>>| (op0 a).c1) ^| (x >>>| (op0 a).c2))

inline_for_extraction
val _Sigma1: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
inline_for_extraction
let _Sigma1 #a #m x = Spec.((x >>>| (op0 a).c3) ^| (x >>>| (op0 a).c4) ^| (x >>>| (op0 a).c5))

inline_for_extraction
val _sigma0: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
inline_for_extraction
let _sigma0 #a #m x = Spec.((x >>>| (op0 a).e0) ^| (x >>>| (op0 a).e1) ^| (x >>| (op0 a).e2))

inline_for_extraction
val _sigma1: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
inline_for_extraction
let _sigma1 #a #m x = Spec.((x >>>| (op0 a).e3) ^| (x >>>| (op0 a).e4) ^| (x >>| (op0 a).e5))

noextract
let _Ch_lemma #a #m x y z :
  Lemma (vec_v (_Ch #a #m x y z) ==
         Lib.Sequence.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i])) =
        Lib.Sequence.eq_intro (vec_v (_Ch #a #m x y z))
        (Lib.Sequence.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))

noextract
let _Maj_lemma #a #m x y z :
  Lemma (vec_v (_Maj #a #m x y z) ==
         Lib.Sequence.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i])) =
        Lib.Sequence.eq_intro (vec_v (_Maj #a #m x y z))
        (Lib.Sequence.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))

noextract
let _Sigma0_lemma #a #m x :
  Lemma (vec_v (_Sigma0 #a #m x) ==
         Lib.Sequence.map (Spec._Sigma0 a) (vec_v x)) =
        Lib.Sequence.eq_intro (vec_v (_Sigma0 #a #m x)) (Lib.Sequence.map (Spec._Sigma0 a) (vec_v x))

noextract
let _Sigma1_lemma #a #m x :
  Lemma (vec_v (_Sigma1 #a #m x) ==
         Lib.Sequence.map (Spec._Sigma1 a) (vec_v x)) =
        Lib.Sequence.eq_intro (vec_v (_Sigma1 #a #m x)) (Lib.Sequence.map (Spec._Sigma1 a) (vec_v x))

noextract
let _sigma0_lemma #a #m x :
  Lemma (vec_v (_sigma0 #a #m x) ==
         Lib.Sequence.map (Spec._sigma0 a) (vec_v x)) =
        Lib.Sequence.eq_intro (vec_v (_sigma0 #a #m x)) (Lib.Sequence.map (Spec._sigma0 a) (vec_v x))

noextract
let _sigma1_lemma #a #m x :
  Lemma (vec_v (_sigma1 #a #m x) ==
         Lib.Sequence.map (Spec._sigma1 a) (vec_v x)) =
        Lib.Sequence.eq_intro (vec_v (_sigma1 #a #m x)) (Lib.Sequence.map (Spec._sigma1 a) (vec_v x))





