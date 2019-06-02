module Hacl.Impl.Bignum.Division

open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.Mul

open Lib.IntTypes
open Lib.Math.Algebra
open Lib.Buffer
open Lib.Loops

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Shift
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Multiplication
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
  let inv h _ = live h r_i /\ live h mod /\ live h mod1 /\ live h tmp /\
                modifies4 mod r_i mod1 tmp h0 h in

  for 0ul count inv (fun i ->
    bn_rshift1 mod mod1;
    if bn_is_geq r_i mod
      then (let _ = bn_sub r_i mod tmp in copy r_i tmp); // in-place sub?
    copy mod mod1
  );

  pop_frame()

val calc_bits_test:
     #aLen:bn_len_strict
  -> a:lbignum aLen
  -> ind:size_t{v ind / 64 < v aLen}
  -> Stack size_t
    (requires fun h -> live h a)
    (ensures  fun h0 _ h1 -> modifies0 h0 h1 /\ h0 == h1)
let rec calc_bits_test #aLen a ind =
  if ind =. 0ul then 0ul else
  if bn_is_bit_set a ind then ind else calc_bits_test a (ind -! 1ul)

val calc_bits:
     #aLen:bn_len_strict
  -> a:lbignum aLen
  -> Stack size_t
    (requires fun h -> live h a)
    (ensures  fun h0 _ h1 -> modifies0 h0 h1 /\ h0 == h1 /\ live h1 a)
let calc_bits #aLen a = calc_bits_test a (aLen *! 64ul -! 1ul)

// res = a % n
val bn_remainder:
     #aLen:bn_len_strict
  -> #modLen:bn_len_strict
  -> a:lbignum aLen
  -> mod:lbignum modLen
  -> res:lbignum modLen
  -> Stack unit
    (requires fun h -> live h a /\ live h mod /\ live h res)
    (ensures fun h0 _ h1 ->
        live h1 a /\ live h1 mod /\ live h1 res /\
        modifies1 res h0 h1)
let bn_remainder #aLen #modLen a mod res =
  push_frame();

  let modBits = calc_bits mod in
  let aBits = calc_bits a in
  let realALen = aBits /. 64ul in

  if aBits >=. modBits then begin
    assume (v aBits >= v modBits);
    let diffBits = aBits -! modBits in // +1?
    let modk = diffBits /. 64ul in
    assume ((v modLen + v modk + 1) * 64 < max_size_t);
    assume (v modLen + v modk + 1 > 0);
    assume (v (modLen +! modk) + 1 > 0);
    let mod1Len:bn_len = modLen +! modk +! 1ul in
    // this push_frame() is required, because otherwise
    // kremlin says it can't generate buffer allocation
    // because of the variable length.
    push_frame();
    let mod1 = create mod1Len (uint 0) in
    bn_lshift mod diffBits mod1;
    assume (v mod1Len <= v aLen);

    let res1 = create aLen (uint 0) in
    copy (sub res1 0ul aLen) a;

    assume (v diffBits + 1 < max_size_t);
    bn_remainder_core res1 mod1 (diffBits +! 1ul);

    copy res (sub res1 0ul modLen);
    pop_frame()
  end
  else
  begin
    // what's wrong???
    if aLen >=. modLen
    then (assert (v aLen >= v modLen); admit(); copy res (sub a 0ul modLen))
    else (admit(); copy (sub res 0ul aLen) a)
  end;

  pop_frame()

val bn_modular_add:
     #len:bn_len_strict{(v len + 1) * 64 < max_size_t}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h b /\ live h res /\
       as_snat h n > 1)
    (ensures  fun h0 _ h1 ->
         live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
         modifies (loc res) h0 h1 /\
         (let n' = as_snat h0 n in
         to_fe #n' (as_snat h1 res) = to_fe (as_snat h0 a) +% to_fe (as_snat h0 b)))
let bn_modular_add #len n a b res =
  let h0 = FStar.HyperStack.ST.get () in
  push_frame ();
  assert (v len < max_size_t);
  let res' = create (len +! 1ul) (uint 0) in
  bn_add_full a b res';
  bn_remainder res' n res;
  pop_frame ();
  let h1 = FStar.HyperStack.ST.get () in
  assume (let n' = as_snat h0 n in
          to_fe #n' (as_snat h1 res) =
          to_fe (as_snat h0 a) +% to_fe (as_snat h0 b))

val bn_modular_mul:
     #len:bn_len_strict{(v len + v len) * 64 < max_size_t}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h b /\ live h res /\
       as_snat h n > 1)
    (ensures  fun h0 _ h1 ->
         live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
         modifies (loc res) h0 h1 /\
         (let n' = as_snat h0 n in
         to_fe #n' (as_snat h1 res) = to_fe (as_snat h0 a) *% to_fe (as_snat h0 b)))
let bn_modular_mul #len n a b res =
  let h0 = FStar.HyperStack.ST.get () in
  push_frame ();
  let res' = create (len +! len) (uint 0) in
  bn_mul a b res';
  bn_remainder res' n res;
  pop_frame ();
  let h1 = FStar.HyperStack.ST.get () in
  assume (let n' = as_snat h0 n in
          to_fe #n' (as_snat h1 res) =
          to_fe (as_snat h0 a) *% to_fe (as_snat h0 b))
