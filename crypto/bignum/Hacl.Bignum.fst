module Hacl.Bignum

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo
open Hacl.Bignum.Fscalar
open Hacl.Bignum.Fsum
open Hacl.Bignum.Fdifference
open Hacl.Bignum.Fproduct
open Hacl.Bignum.Crecip

module U32 = FStar.UInt32


val fsum:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b
      /\ red_c h a len /\ red_c h b len))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ red_c h0 a len /\ red_c h0 b len
      /\ live h1 a /\ modifies_1 a h0 h1
      /\ eval h1 a = eval h0 a + eval h0 b))
let fsum a b =
  let h0 = ST.get() in
  fsum_ a b clen;
  let h1 = ST.get() in
  assume (eval h1 a = eval h0 a + eval h0 b)

#set-options "--initial_fuel 0 --max_fuel 0"

val fdifference:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ add_zero_pre (as_seq h b)
      /\ Hacl.Bignum.Fdifference.Spec.gte_limbs (as_seq h a) (add_zero_spec (as_seq h b)) len))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b
      /\ live h1 a /\ modifies_1 a h0 h1
      /\ eval h1 a % prime = (eval h0 b - eval h0 a) % prime ))
let fdifference a b =
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp = create limb_zero clen in
  blit b 0ul tmp 0ul clen;
  let h = ST.get() in
  Hacl.Bignum.Fproduct.Spec.lemma_whole_slice (as_seq h b);
  Hacl.Bignum.Fproduct.Spec.lemma_whole_slice (as_seq h tmp);
  FStar.Seq.lemma_eq_intro (as_seq h b) (as_seq h tmp);
  add_zero tmp;
  fdifference_ a tmp clen;
  let h1 = ST.get() in
  pop_frame();
  let hfin = ST.get() in
  assume (eval hfin a % prime = (eval hinit b - eval hinit a) % prime)

open Hacl.Bignum.Fscalar.Spec
open Hacl.Bignum.Fproduct.Spec

val fscalar:
  a:felem ->
  b:felem{disjoint a b} ->
  s:limb ->
  Stack unit
    (requires (fun h -> live h b /\ live h a
      /\ carry_wide_pre (fscalar_spec (Seq.create len wide_zero) (as_seq h b) s len) 0
      /\ carry_top_wide_pre (carry_wide_spec (fscalar_spec (Seq.create len wide_zero) (as_seq h b) s len) 0)
      /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (fscalar_spec (Seq.create len wide_zero) (as_seq h b) s len) 0)) ))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ modifies_1 a h0 h1 /\ live h1 a
      /\ eval h1 a = eval h0 b * v s))
let fscalar output b s =
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp = create wide_zero clen in
  fscalar tmp b s;
  carry_wide_ tmp 0ul;
  carry_top_wide tmp;
  copy_from_wide_ output tmp clen;
  let h1 = ST.get() in
  pop_frame();
  let hfin = ST.get() in
  assume (eval hfin output = eval hinit b * v s)


val fmul:
  output:felem ->
  a:felem{disjoint output a} ->
  b:felem{disjoint output b} ->
  Stack unit
    (requires (fun h -> live h output /\ live h a /\ live h b
      /\ fmul_pre (as_seq h a) (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 output /\ live h0 a /\ live h0 b 
      /\ modifies_1 output h0 h1 /\ live h1 output
      /\ eval h1 output % prime = (eval h0 a * eval h0 b) % prime
      ))
let fmul output a b =
  let h0 = ST.get() in
  fmul output a b;
  let h1 = ST.get() in
  assume (eval h1 output % prime = (eval h0 a * eval h0 b) % prime)


#set-options "--lax"

val fsquare_times:
  output:felem ->
  input:felem ->
  count:ctr ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let fsquare_times output input count =
  fsquare_times output input count


val crecip:
  output:felem ->
  input:felem ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let crecip output input =
  crecip output input
