module Hacl.Impl.Bignum.Division

open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Loops

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Shift
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Addition


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_remainder_core:
     #rLen:bn_len
  -> #modLen:bn_len{v modLen <= v rLen}
  -> r_i:lbignum rLen
  -> mod:lbignum modLen
  -> count:size_t
  -> Stack unit
        (requires (fun h -> live h r_i /\ live h mod))
        (ensures (fun h0 _ h1 -> live h1 r_i /\ live h1 mod /\ modifies2 mod r_i h0 h1))
let bn_remainder_core #rLen #modLen r_i mod count =
  push_frame();
  let mod1 = create modLen (uint 0) in
  let tmp = create rLen (uint 0) in

  let h0 = FStar.HyperStack.ST.get () in
  let inv h _ = live h r_i /\ live h mod /\ live h mod1 /\ live h tmp /\ modifies4 mod r_i mod1 tmp h0 h in

  for 0ul count inv (fun i ->
    let ind = count -! i in
    bn_rshift1 mod mod1;
    let tmp_b = bn_is_greater mod r_i in
    if not tmp_b then (let _ = bn_sub r_i mod tmp in copy r_i tmp); // in-place sub?
    copy mod mod1
  );

  pop_frame()

// res = a % n
// TODO it should also support case for modLen > aLen
val bn_remainder:
     #aLen:bn_len{v aLen + 1 < max_size_t}
  -> #modLen:bn_len{v modLen <= v aLen}
  -> #resLen:bn_len{v resLen <= v modLen}
  -> a:lbignum aLen
  -> mod:lbignum modLen
  -> res:lbignum resLen
  -> Stack unit
    (requires fun h -> live h a /\ live h mod /\ live h res)
    (ensures fun h0 _ h1 ->
        live h1 a /\ live h1 mod /\ live h1 res /\
        modifies1 res h0 h1)
let bn_remainder #aLen #modLen #resLen a mod res =
  push_frame();
  let diffBits = 64ul *. (aLen -! modLen) in
  let modk = diffBits /. 64ul in
  assume (v modLen + v modk + 1 < max_size_t);
  let mod1Len = modLen +! modk +! 1ul in
  let mod1 = create mod1Len (uint 0) in
  bn_lshift mod diffBits mod1;
  let a1Len = aLen +! 1ul in
  let r0 = create a1Len (uint 0) in
  copy (sub r0 0ul aLen) a;
  bn_remainder_core r0 mod1 diffBits;
  copy res (sub r0 0ul resLen);
  pop_frame()
