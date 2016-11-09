module Hacl.EC.Curve25519.Bignum

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt64

open FStar.Buffer
open FStar.Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Utils

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"


(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128


let bound64 h (b:bigint_wide) : GTot Type0 =
  live h b /\ (let open Hacl.UInt128 in
  v (get h b 0) < pow2 64
  /\ v (get h b 1) < pow2 64
  /\ v (get h b 2) < pow2 64
  /\ v (get h b 3) < pow2 64
  /\ v (get h b 4) < pow2 64)


val copy_bigint: output:bigint -> input:bigint{disjoint input output} -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1
      /\ v (get h0 input 0) = v (get h1 output 0)
      /\ v (get h0 input 1) = v (get h1 output 1)
      /\ v (get h0 input 2) = v (get h1 output 2)
      /\ v (get h0 input 3) = v (get h1 output 3)
      /\ v (get h0 input 4) = v (get h1 output 4)
      /\ eval h1 output 5 = eval h0 input 5))
let copy_bigint output i =
  let i0 = i.(0ul) in
  let i1 = i.(1ul) in
  let i2 = i.(2ul) in
  let i3 = i.(3ul) in
  let i4 = i.(4ul) in
  let h0 = ST.get() in
  update_5 output i0 i1 i2 i3 i4;
  let h1 = ST.get() in
  Hacl.EC.Curve25519.Bignum.Lemmas.Utils.lemma_eval_bigint_5 h0 i;
  Hacl.EC.Curve25519.Bignum.Lemmas.Utils.lemma_eval_bigint_5 h1 output


val copy_to_bigint': output:bigint -> input:bigint_wide{disjoint input output} -> Stack unit
    (requires (fun h -> live h output /\ bound64 h input))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input
      /\ H128.v (get h0 input 0) = v (get h1 output 0)
      /\ H128.v (get h0 input 1) = v (get h1 output 1)
      /\ H128.v (get h0 input 2) = v (get h1 output 2)
      /\ H128.v (get h0 input 3) = v (get h1 output 3)
      /\ H128.v (get h0 input 4) = v (get h1 output 4) ))
let rec copy_to_bigint' output b =
  Math.Lemmas.pow2_lt_compat 128 64;
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let open Hacl.UInt128 in
  Math.Lemmas.modulo_lemma (v b0) (pow2 64);
  Math.Lemmas.modulo_lemma (v b1) (pow2 64);
  Math.Lemmas.modulo_lemma (v b2) (pow2 64);
  Math.Lemmas.modulo_lemma (v b3) (pow2 64);
  Math.Lemmas.modulo_lemma (v b4) (pow2 64);
  update_5 output (Hacl.Cast.sint128_to_sint64 b0)
                 (Hacl.Cast.sint128_to_sint64 b1)
                 (Hacl.Cast.sint128_to_sint64 b2)
                 (Hacl.Cast.sint128_to_sint64 b3)
                 (Hacl.Cast.sint128_to_sint64 b4)


val copy_to_bigint:
  output:bigint ->
  input:bigint_wide{disjoint input output} ->
  Stack unit
    (requires (fun h -> live h output /\ norm_wide h input))
    (ensures (fun h0 _ h1 -> modifies_1 output h0 h1 /\ norm h1 output /\ norm_wide h0 input
      /\ eval_wide h0 input norm_length = eval h1 output norm_length ))
let copy_to_bigint output b =
  let h0 = ST.get() in
  Math.Lemmas.pow2_lt_compat 64 51;
  copy_to_bigint' output b;
  let h1 = ST.get() in
  Hacl.EC.Curve25519.Bignum.Lemmas.Utils.lemma_eval_bigint_wide_5 h0 b;
  Hacl.EC.Curve25519.Bignum.Lemmas.Utils.lemma_eval_bigint_5 h1 output


val copy_to_bigint_wide': output:bigint_wide -> input:bigint{disjoint input output} -> Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h1 output /\ modifies_1 output h0 h1
      /\ H128.v (get h1 output 0) = v (get h0 input 0)
      /\ H128.v (get h1 output 1) = v (get h0 input 1)
      /\ H128.v (get h1 output 2) = v (get h0 input 2)
      /\ H128.v (get h1 output 3) = v (get h0 input 3)
      /\ H128.v (get h1 output 4) = v (get h0 input 4) ))
let rec copy_to_bigint_wide' output b =
  Math.Lemmas.pow2_lt_compat 128 64;
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  update_wide_5 output (Hacl.Cast.sint64_to_sint128 b0)
                      (Hacl.Cast.sint64_to_sint128 b1)
                      (Hacl.Cast.sint64_to_sint128 b2)
                      (Hacl.Cast.sint64_to_sint128 b3)
                      (Hacl.Cast.sint64_to_sint128 b4)


val copy_to_bigint_wide: output:bigint_wide -> input:bigint{disjoint input output} -> Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h1 output /\ modifies_1 output h0 h1
      /\ H128.v (get h1 output 0) = v (get h0 input 0)
      /\ H128.v (get h1 output 1) = v (get h0 input 1)
      /\ H128.v (get h1 output 2) = v (get h0 input 2)
      /\ H128.v (get h1 output 3) = v (get h0 input 3)
      /\ H128.v (get h1 output 4) = v (get h0 input 4)
      /\ eval_wide h1 output norm_length = eval h0 input norm_length))
let copy_to_bigint_wide output b =
  let h0 = ST.get() in
  copy_to_bigint_wide' output b;
  let h1 = ST.get() in
  Hacl.EC.Curve25519.Bignum.Lemmas.Utils.lemma_eval_bigint_5 h0 b;
  Hacl.EC.Curve25519.Bignum.Lemmas.Utils.lemma_eval_bigint_wide_5 h1 output


val modulo:
  output:bigint ->
  input:bigint_wide{disjoint input output} ->
  Stack unit
    (requires (fun h -> live h input /\ live h output
      /\ Hacl.EC.Curve25519.Bignum.Modulo.Lemmas.satisfiesModuloConstraints h input
      /\ length input >= 2*norm_length - 1 ))
    (ensures (fun h0 _ h1 -> norm h1 output /\ live h1 input /\ modifies_2 output input h0 h1
      /\ live h0 input /\ length input >= 2*norm_length-1
      /\ eval h1 output norm_length % reveal prime = eval_wide h0 input (2*norm_length-1) % reveal prime
      /\ modifies_2 output input h0 h1))
let modulo output b =
  let h0 = ST.get() in
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_degree b;
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients_wide b;
  copy_to_bigint output b


val fsum: a:bigint{length a >= norm_length + 1} -> b:bigint{disjoint a b} -> Stack unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 _ h1 -> norm h1 a /\ modifies_1 a h0 h1 /\ norm h0 a /\ norm h0 b
      /\ eval h1 a norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime))
let fsum a b =
  Math.Lemmas.pow2_lt_compat 63 52;
  Hacl.EC.Curve25519.Bignum.Fsum.fsum' a b;
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients a


let lemma_norm h (b:bigint) : Lemma
  (requires (norm h b))
  (ensures (norm h b /\ v (get h b 0) < pow2 51 /\ v (get h b 1) < pow2 51
    /\ v (get h b 2) < pow2 51 /\ v (get h b 3) < pow2 51 /\ v (get h b 4) < pow2 51))
  = ()


let lemma_eq h (b:bigint{live h b}) h' (b':bigint{live h' b'}): Lemma
  (requires (Buffer.equal h b h' b'))
  (ensures (v (get h b 0) = v (get h' b' 0)
    /\ v (get h b 1) = v (get h' b' 1)
    /\ v (get h b 2) = v (get h' b' 2)
    /\ v (get h b 3) = v (get h' b' 3)
    /\ v (get h b 4) = v (get h' b' 4) ))
  = ()


let lemma_eq' h (b:bigint{norm h b}) h' (b':bigint{live h' b'}): Lemma
  (requires (v (get h b 0) = v (get h' b' 0)
    /\ v (get h b 1) = v (get h' b' 1)
    /\ v (get h b 2) = v (get h' b' 2)
    /\ v (get h b 3) = v (get h' b' 3)
    /\ v (get h b 4) = v (get h' b' 4)))
  (ensures (norm h' b'))
  = ()


let lemma_eq_norm h h' (b:bigint) (b':bigint) : Lemma
  (requires (norm h b /\ live h' b' /\ Buffer.equal h b h' b'))
  (ensures (norm h' b'))
  = lemma_norm h b; lemma_eq h b h' b'


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

assume val lemma_mod_sub_distr_r: a:nat -> b:nat -> p:pos ->
  Lemma (requires (True))
        (ensures  ((a - b) % p = ((a % p) - b) % p))

val lemma_mod_fdifference: a:nat -> b:nat -> c:nat -> p:pos ->
  Lemma (requires (a % p = c % p))
        (ensures  ((a - b) % p = ((c - b) % p)))
let lemma_mod_fdifference a b c p =
  lemma_mod_sub_distr_r a b p;
  lemma_mod_sub_distr_r c b p;
  ()


#reset-options "--z3timeout 200 --initial_fuel 0 --max_fuel 0"

val fdifference: a:bigint{length a >= norm_length+1} -> b:bigint{disjoint a b} -> Stack unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 _ h1 -> norm h0 b /\ norm h0 a /\ norm h1 a /\ modifies_1 a h0 h1
      /\ eval h1 a norm_length % reveal prime = (eval h0 b norm_length - eval h0 a norm_length) % reveal prime))
let fdifference a b =
  let hinit = ST.get() in
  push_frame ();
  let h0 = ST.get() in
  let b' = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let h0' = ST.get() in
    lemma_eq_norm hinit h0' b b;
    Hacl.EC.Curve25519.Bigint.eval_eq_lemma hinit h0' b b 5;
    lemma_eq_norm hinit h0' a a;
    Buffer.no_upd_lemma_0 h0 h0' b;
  copy_bigint b' b;
  let h1 = ST.get() in
    lemma_eq' hinit b h1 b';
    Hacl.EC.Curve25519.Bigint.eval_eq_lemma h0 h0' b b 5;
    cut (eval h1 b' 5 = eval h0 b 5);
  Hacl.EC.Curve25519.Bignum.Fdifference.add_big_zero b';
  let h2 = ST.get() in
    cut(modifies_1 b' h0' h2);
    Buffer.no_upd_lemma_1 h0' h2 b' a;
    lemma_eq_norm hinit h2 a a;
    Hacl.EC.Curve25519.Bigint.eval_eq_lemma hinit h2 a a 5;
    cut (eval h2 b' 5 % (reveal prime) = eval h1 b' 5 % (reveal prime));
  Hacl.EC.Curve25519.Bignum.Fdifference.fdifference' a b';
  let h3 = ST.get() in
    Hacl.EC.Curve25519.Bigint.eval_eq_lemma h2 h3 b' b' 5;
    cut (eval h3 a 5 = eval h2 b' 5 - eval h2 a 5);
    Math.Lemmas.pow2_lt_compat 63 53;
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients a;
  let h4 = ST.get() in
    cut (eval h4 a 5 % reveal prime = eval h3 a 5 % reveal prime);
    cut (eval h4 a 5 % reveal prime = (eval h2 b' 5 - eval h2 a 5) % reveal prime);
    cut (eval h4 a 5 % reveal prime = (eval h2 b' 5 - eval hinit a 5) % reveal prime);
    lemma_mod_fdifference (eval h2 b' 5) (eval hinit a 5) (eval hinit b 5) (reveal prime);
    cut (eval h4 a 5 % reveal prime = (eval hinit b 5 - eval hinit a 5) % reveal prime);
  pop_frame();
  let hfin = ST.get() in
    lemma_eq_norm h4 hfin a a;
    Hacl.EC.Curve25519.Bigint.eval_eq_lemma h4 hfin a a 5;
    ()


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val fscalar:
    res:bigint -> b:bigint{disjoint res b} -> s:s64 -> Stack unit
  (requires (fun h -> live h res /\ norm h b))
  (ensures (fun h0 _ h1 -> norm h0 b /\ norm h1 res /\ modifies_1 res h0 h1
    /\ (eval h1 res norm_length % reveal prime = ((eval h0 b norm_length * v s) % reveal prime))))
let fscalar res b s =
  let hinit = ST.get() in
  push_frame ();
  let h0 = ST.get() in
  let tmp = create (Hacl.Cast.uint64_to_sint128 0uL) (6ul) in
  let h0' = ST.get() in
  lemma_eq_norm hinit h0' b b;
  Hacl.EC.Curve25519.Bigint.eval_eq_lemma hinit h0' b b 5;
  Hacl.EC.Curve25519.Bignum.Fscalar.scalar' tmp b s;
  let h1 = ST.get() in
  cut (eval_wide h1 tmp 5 = eval hinit b 5 * v s);
  Math.Lemmas.pow2_lt_compat 127 115;
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients_wide tmp;
  let h2 = ST.get() in
  cut (eval_wide h2 tmp 5 % reveal prime = eval_wide h1 tmp 5 % reveal prime);
  Math.Lemmas.pow2_lt_compat 64 51;
  copy_to_bigint res tmp;
  let h3 = ST.get() in
  cut (eval h3 res norm_length = eval_wide h2 tmp norm_length);
  cut (eval h3 res norm_length % reveal prime = eval_wide h1 tmp norm_length % reveal prime);
  cut (eval h3 res norm_length % reveal prime = (eval hinit b norm_length * v s) % reveal prime);
  pop_frame();
  let hfin = ST.get() in
  lemma_eq_norm h3 hfin res res;
  lemma_eq_norm hinit hfin b b;
  Hacl.EC.Curve25519.Bigint.eval_eq_lemma h3 hfin res res 5;
  cut ((eval hfin res norm_length % reveal prime) = ((eval hinit b norm_length * v s) % reveal prime));
  cut (modifies_1 res hinit hfin);
  cut (norm hinit b);
  cut (norm hfin res);
  cut (HyperStack.equal_domains hinit hfin)


val fmul: res:bigint -> a:bigint{disjoint res a} -> b:bigint{disjoint res b} -> Stack unit
    (requires (fun h -> live h res /\ norm h a /\ norm h b))
    (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1
      /\ norm h0 a /\ norm h0 b /\ norm h1 res
      /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime ))
let fmul res a b =
  let hinit = ST.get() in
  push_frame ();
  let h0 = ST.get() in
  let tmp = create (Hacl.Cast.uint64_to_sint128 0uL) 9ul in
  let h1 = ST.get() in
  lemma_eq_norm hinit h1 a a;
  lemma_eq_norm hinit h1 b b;
  Hacl.EC.Curve25519.Bigint.eval_eq_lemma hinit h1 a a 5;
  Hacl.EC.Curve25519.Bigint.eval_eq_lemma hinit h1 b b 5;
  Hacl.EC.Curve25519.Bignum.Fproduct.multiplication tmp a b;
  let h2 = ST.get() in
  cut (eval_wide h2 tmp 9 = eval hinit a 5 * eval hinit b 5);
  assert_norm(pow2 102 = 5070602400912917605986812821504);
  assert_norm(pow2 127 = 170141183460469231731687303715884105728);
  modulo res tmp;
  let h3 = ST.get() in
  cut (eval h3 res 5 % reveal prime = (eval hinit a 5 * eval hinit b 5) % reveal prime);
  pop_frame();
  let hfin = ST.get() in
  Hacl.EC.Curve25519.Bigint.eval_eq_lemma h3 hfin res res 5;
  lemma_eq_norm h3 hfin res res;
  ()


val fsquare: res:bigint -> a:bigint{disjoint res a} -> Stack unit
    (requires (fun h -> live h res /\ norm h a))
    (ensures (fun h0 _ h1 -> norm h1 res /\ norm h0 a /\ modifies_1 res h0 h1
      /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 a norm_length) % reveal prime))
let fsquare res a =
  fmul res a a
