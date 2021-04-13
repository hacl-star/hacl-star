module Hacl.Bignum.Definitions

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module S = Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val blocks: x:size_t{v x > 0} -> m:size_t{v m > 0} -> r:size_t{v r == S.blocks (v x) (v m)}
let blocks x m = (x -. 1ul) /. m +. 1ul

inline_for_extraction noextract
val blocks0: x:size_t -> m:size_t{v m > 0} -> r:size_t{v r == S.blocks0 (v x) (v m)}
let blocks0 x m = if x =. 0ul then 1ul else (x -. 1ul) /. m +. 1ul

inline_for_extraction noextract
let limb_t = S.limb_t

inline_for_extraction noextract
let limb (t:limb_t) = S.limb t

inline_for_extraction noextract
let lbignum (t:limb_t) len = lbuffer (limb t) len

noextract
val bn_v: #t:limb_t -> #len:size_t -> h:mem -> b:lbignum t len -> GTot nat
let bn_v #t #len h b = S.bn_v #t #(v len) (as_seq h b)
