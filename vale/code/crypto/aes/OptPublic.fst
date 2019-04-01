module OptPublic

open FStar.Seq
open Types_s
open Math.Poly2_s
open Math.Poly2.Bits_s
open GF128_s
open GF128
open Words_s

let shift_gf128_key_1 (h:poly) : poly =
  shift_key_1 128 gf128_modulus_low_terms h

let rec g_power (a:poly) (n:nat) : poly =
  if n = 0 then zero else // arbitrary value for n = 0
  if n = 1 then a else
  a *~ g_power a (n - 1)

let gf128_power (h:poly) (n:nat) : poly = shift_gf128_key_1 (g_power h n)

let hkeys_reqs_pub (hkeys:seq quad32) (h_BE:quad32) : Prop_s.prop0
  = 
  let h = of_quad32 (reverse_bytes_quad32 (reverse_bytes_quad32 h_BE)) in
  length hkeys >= 8 /\
  of_quad32 (index hkeys 0) == gf128_power h 1 /\
  of_quad32 (index hkeys 1) == gf128_power h 2 /\
  index hkeys 2 == h_BE /\
  of_quad32 (index hkeys 3) == gf128_power h 3 /\
  of_quad32 (index hkeys 4) == gf128_power h 4 /\
  index hkeys 5 == Mkfour 0 0 0 0 /\ // Not needed but we want injectivity
  of_quad32 (index hkeys 6) == gf128_power h 5 /\
  of_quad32 (index hkeys 7) == gf128_power h 6 

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

open FStar.List.Tot
open Math.Poly2.Bits

let get_hkeys_reqs h_BE =
  let h = of_quad32 (reverse_bytes_quad32 (reverse_bytes_quad32 h_BE)) in
  let l = [to_quad32 (gf128_power h 1);
     to_quad32 (gf128_power h 2);
     h_BE;
     to_quad32 (gf128_power h 3);
     to_quad32 (gf128_power h 4);
     Mkfour 0 0 0 0;
     to_quad32 (gf128_power h 5);
     to_quad32 (gf128_power h 6)] in
  assert_norm (length l = 8);
  let s = Seq.seq_of_list l in
  Seq.lemma_seq_of_list_induction l;
  Seq.lemma_seq_of_list_induction (tl l);
  Seq.lemma_seq_of_list_induction (tl (tl l));
  Seq.lemma_seq_of_list_induction (tl (tl (tl l)));
  Seq.lemma_seq_of_list_induction (tl (tl (tl (tl l))));
  Seq.lemma_seq_of_list_induction (tl (tl (tl (tl (tl l)))));
  Seq.lemma_seq_of_list_induction (tl (tl (tl (tl (tl (tl l))))));  
  Seq.lemma_seq_of_list_induction (tl (tl (tl (tl (tl (tl (tl l))))))); 
  Seq.lemma_seq_of_list_induction (tl (tl (tl (tl (tl (tl (tl (tl l)))))))); 
  lemma_of_to_quad32 (gf128_power h 1);
  lemma_of_to_quad32 (gf128_power h 2);
  lemma_of_to_quad32 (gf128_power h 3);
  lemma_of_to_quad32 (gf128_power h 4);
  lemma_of_to_quad32 (gf128_power h 5);
  lemma_of_to_quad32 (gf128_power h 6);  
  assert (hkeys_reqs_pub s h_BE);
  s

open FStar.UInt

let lemma_of_quad32_inj (q q':quad32) : Lemma
  (requires of_quad32 q == of_quad32 q')
  (ensures q == q')
  = lemma_to_of_quad32 q; lemma_to_of_quad32 q'
    
let get_hkeys_reqs_injective h_BE s1 s2 =
  lemma_of_quad32_inj (Seq.index s1 0) (Seq.index s2 0);
  lemma_of_quad32_inj (Seq.index s1 1) (Seq.index s2 1);
  lemma_of_quad32_inj (Seq.index s1 3) (Seq.index s2 3);
  lemma_of_quad32_inj (Seq.index s1 4) (Seq.index s2 4);
  lemma_of_quad32_inj (Seq.index s1 6) (Seq.index s2 6);
  lemma_of_quad32_inj (Seq.index s1 7) (Seq.index s2 7);  
  assert (Seq.equal s1 s2)
