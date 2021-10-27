module Hacl.Impl.K256.Point

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

open Hacl.K256.Field

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// (_X, _Y, _Z)
inline_for_extraction noextract
let point = lbuffer uint64 (nlimb *! 3ul)


inline_for_extraction noextract
let getx (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul nlimb /\ h0 == h1)
  = sub p 0ul nlimb

inline_for_extraction noextract
let gety (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p nlimb nlimb /\ h0 == h1)
  = sub p nlimb nlimb

inline_for_extraction noextract
let getz (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p (2ul *! nlimb) nlimb /\ h0 == h1)
  = sub p (2ul *! nlimb) nlimb
 
noextract
let point_inv (h:mem) (p:point) =
  fe_lt_prime h (gsub p 0ul nlimb) /\
  fe_lt_prime h (gsub p nlimb nlimb) /\
  fe_lt_prime h (gsub p (2ul *! nlimb) nlimb)


noextract
let point_as_nat3 (h:mem) (p:point) =
  (as_nat h (gsub p 0ul nlimb),
   as_nat h (gsub p nlimb nlimb),
   as_nat h (gsub p (2ul *! nlimb) nlimb))

noextract
let point_as_nat3_proj (h:mem) (p:point{point_inv h p}) : GTot Spec.K256.proj_point =
  (as_nat h (gsub p 0ul nlimb),
   as_nat h (gsub p nlimb nlimb),
   as_nat h (gsub p (2ul *! nlimb) nlimb))

noextract
let point_eval (h:mem) (p:point) =
  (feval h (gsub p 0ul nlimb),
   feval h (gsub p nlimb nlimb),
   feval h (gsub p (2ul *! nlimb) nlimb))
