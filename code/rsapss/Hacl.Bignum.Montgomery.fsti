module Hacl.Bignum.Montgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
module S = Hacl.Spec.Bignum.Montgomery


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val mod_inv_u64: n0:uint64 ->
  Stack uint64
  (requires fun h -> True)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.mod_inv_u64 n0)


val precomp_r2_mod_n:
    nLen:size_t{0 < v nLen /\ 128 * (v nLen + 1) <= max_size_t}
  -> modBits:size_t{0 < v modBits /\ v nLen == v (blocks modBits 64ul)}
  -> n:lbignum nLen
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h -> live h n /\ live h res /\ disjoint n res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.precomp_r2_mod_n (v modBits) (as_seq h0 n))


val mont_reduction:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen +! rLen)
  -> res:lbignum rLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h c /\ live h res /\
    disjoint res n /\ disjoint res c /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    as_seq h1 res == S.mont_reduction #(v nLen) #(v rLen) (as_seq h0 n) mu (as_seq h0 c))


val to_mont:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> aM:lbignum rLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h r2 /\ live h a /\ live h aM /\
    disjoint a r2 /\ disjoint a n /\ disjoint a aM /\
    disjoint n r2 /\ disjoint n aM /\ disjoint r2 aM)
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    as_seq h1 aM == S.to_mont #(v nLen) #(v rLen) (as_seq h0 n) mu (as_seq h0 r2) (as_seq h0 a))


val from_mont:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen
  -> a:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h aM /\
    disjoint aM a /\ disjoint aM n /\ disjoint a n)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.from_mont #(v nLen) #(v rLen) (as_seq h0 n) mu (as_seq h0 aM))


val mont_mul:
    nLen:size_t
  -> rLen:size_t{v rLen = v nLen + 1 /\ v rLen + v rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen
  -> bM:lbignum rLen
  -> resM:lbignum rLen ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h bM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM bM /\
    eq_or_disjoint aM resM /\ eq_or_disjoint bM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.mont_mul (as_seq h0 n) mu (as_seq h0 aM) (as_seq h0 bM))
