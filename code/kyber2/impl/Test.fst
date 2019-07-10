module Test

open Impl.Kyber2.Group
//open Lib.Arithmetic.Group

open FStar.Mul
open FStar.HyperStack.All
open Lib.IntTypes
open FStar.Math.Lemmas

module Group = Spec.Kyber2.Group
module MGroup = Impl.Kyber2.GroupMontgomery

#set-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"
(*
val int64_to_int16: a:int64 -> Tot (b:int16{sint_v b = sint_v a @%. S16})

inline_for_extraction
let mod_mask (#t:inttype) (#l:secrecy_level) (m:shiftval t{uint_v m + 1<bits t}) : int_t t l =
  assert_norm(range 1 t);
  pow2_lt_compat (bits t - 1) (uint_v m);
  pow2_le_compat (uint_v m) 0;
  assert(range (pow2 (uint_v m)) t);
  assert(range (pow2 (uint_v m) - 1) t);
  shift_left_lemma (mk_int #t #l 1) m;
  ((mk_int 1) <<. m) -! (mk_int 1)

private
val mod_mask_value: #t:inttype -> #l:secrecy_level -> m:shiftval t{uint_v m + 1 < bits t} ->
  Lemma (v (mod_mask #t #l m) == pow2 (v m) - 1)


let mod_mask_value #t #l m =
  assert_norm(range 1 t);
  pow2_lt_compat (bits t - 1) (uint_v m);
  pow2_le_compat (uint_v m) 0;
  assert(range (pow2 (uint_v m)) t);
  assert(range (pow2 (uint_v m) - 1) t);
  shift_left_lemma (mk_int #t #l 1) m;
  sub_lemma (mk_int #t #l 1 <<. m) (mk_int #t #l 1)

val mod_mask_lemma: #t:inttype -> #l:secrecy_level -> a:int_t t l -> m:shiftval t{uint_v m +1 < bits t}
  -> Lemma (v (a `logand` mod_mask m) == v a % pow2 (v m))
  [SMTPat (a `logand` mod_mask #t m)]

#set-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

let mod_mask_lemma #t #l a m =
  mod_mask_value #t #l m;
  logand_spec #t #l a (mod_mask m);
  if (unsigned t || (v a >= 0)) then
    if(v m = 0) then
      UInt.logand_lemma_1 #(bits t) (v a)
    else
      UInt.logand_mask #(bits t) (v a) (v m)
  else
    begin
    let a1 = v a in
    let a2 = FStar.Int.to_uint a1 in
    assert (a2 = a1 + pow2 (bits t));
    let s = FStar.Int.logand #(bits t) a1 (pow2 (v m) - 1) in
    let u = FStar.UInt.logand #(bits t) a2 (pow2 (v m) -1) in
    if(v m = 0) then
      UInt.logand_lemma_1 #(bits t) a2
    else
      UInt.logand_mask #(bits t) a2 (v m);
    pow2_plus ((bits t) - (v m)) (v m);
    pow2_le_compat (bits t -1) (v m);
    lemma_mod_plus (v a) (pow2 ((bits t) - (v m))) (pow2 (v m))
    end

let csub64_to_16 (a:int64{range (sint_v a) U16}) : Tot (b:int64{sint_v b = sint_v a @%. S16}) =
  let pow16 = (mk_int #S64 #SEC 1) <<. (size 16) in
  shift_left_lemma (mk_int #S64 #SEC 1) (size 16);
  let pow15 = (mk_int #S64 #SEC 1) <<. (size 15) in
  shift_left_lemma (mk_int #S64 #SEC 1) (size 15);
  let a2 = a -! pow15 in
  let mask = a2 >>. size 63 in
  shift_right_lemma a2 (size 63);
  assert_norm (v a2 < 0 ==> v mask = -1 /\ v a2 >= 0 ==> v mask = 0);
  let a3 = a -! pow16 in
  logand_lemma mask pow16;
  a3 +! (mask &. pow16)

let int64_to_int16 a =
  let mask = mod_mask #S64 #SEC (size 16) in
  mod_mask_lemma a (size 16);
  let a2 = a &. mask in
  to_i16 (csub64_to_16 a2)*)

let main () : St C.exit_code =
  push_frame ();
  //let r = op #_ #monoid_plus_t (mk_t 5) (mk_t 3) in
  assert_norm( range 5 S16 /\ range 3 S16);
  let r2 = plus_t (i16 5) (i16 3) in
  let r3 = exp_t (Group.mk_t 2) (size 2) in
  let r4 = exp_t (Group.mk_t 2) (size 10) in
  let r5 = MGroup.one_m in
  pop_frame ();
  C.EXIT_SUCCESS
