module Spec.Chacha20_vec1.Lemmas

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib

open Seq.Create
open Spec.Chacha20
open Spec.Chacha20_vec

module S = Spec.Chacha20
module V = Spec.Chacha20_vec

let state = S.state
let vec_state = V.state


#set-options "--max_fuel 0 --z3rlimit 100"


let state_to_vec_state (s:state) : Tot vec_state =
  let s0 = slice s 0  4  in
  let s1 = slice s 4  8  in
  let s2 = slice s 8  12 in
  let s3 = slice s 12 16 in
  create_4 s0 s1 s2 s3


let vec_state_to_state (s:vec_state) : Tot state =
  let s0 = index s 0 in
  let s1 = index s 1 in
  let s2 = index s 2 in
  let s3 = index s 3 in
  s0 @| s1 @| s2 @| s3


val lemma_state (s:state) : Lemma (vec_state_to_state (state_to_vec_state s) == s)
let lemma_state s =
  let s0 = slice s 0  4  in
  let s1 = slice s 4  8  in
  let s2 = slice s 8  12 in
  let s3 = slice s 12 16 in
  lemma_eq_intro (s0 @| s1 @| s2 @| s3) s


val lemma_vec_state (s:vec_state) : Lemma (state_to_vec_state (vec_state_to_state s) == s)
let lemma_vec_state s =
  let s0 = index s 0 in
  let s1 = index s 1 in
  let s2 = index s 2 in
  let s3 = index s 3 in
  let s' = s0 @| s1 @| s2 @| s3 in
  lemma_eq_intro (slice s' 0   4) s0;
  lemma_eq_intro (slice s' 4   8) s1;
  lemma_eq_intro (slice s' 8  12) s2;
  lemma_eq_intro (slice s' 12 16) s3;
  lemma_eq_intro (create_4 s0 s1 s2 s3) (s)


unfold let eq_states' (s:state) (s':vec_state) : GTot Type0 =
   let s0' = index (index s' 0) 0 in   let s1' = index (index s' 0) 1 in
   let s2' = index (index s' 0) 2 in   let s3' = index (index s' 0) 3 in
   let s4' = index (index s' 1) 0 in   let s5' = index (index s' 1) 1 in
   let s6' = index (index s' 1) 2 in   let s7' = index (index s' 1) 3 in
   let s8' = index (index s' 2) 0 in   let s9' = index (index s' 2) 1 in
   let s10' = index (index s' 2) 2 in  let s11' = index (index s' 2) 3 in
   let s12' = index (index s' 3) 0 in  let s13' = index (index s' 3) 1 in
   let s14' = index (index s' 3) 2 in  let s15' = index (index s' 3) 3 in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   s0' == s0 /\ s1' == s1 /\ s2' == s2 /\ s3' == s3
   /\ s4' == s4 /\ s5' == s5 /\ s6' == s6 /\ s7' == s7
   /\ s8' == s8 /\ s9' == s9 /\ s10' == s10 /\ s11' == s11
   /\ s12' == s12 /\ s13' == s13 /\ s14' == s14 /\ s15' == s15


let eq_states (s:state) (s':vec_state) : GTot Type0 =
  vec_state_to_state s' == s


val lemma_eq_states_intro: s:state -> s':vec_state -> Lemma
  (requires (eq_states' s s'))
  (ensures (eq_states s s'))
let lemma_eq_states_intro s s' =
  lemma_eq_intro (vec_state_to_state s') s


let quarter_round_vec (s:vec_state) : Tot vec_state =
  let s = V.line 0 1 3 16ul s in
  let s = V.line 2 3 1 12ul s in
  let s = V.line 0 1 3 8ul  s in
  let s = V.line 2 3 1 7ul  s in
  s


let lined (a:t) (b:t) (c:t) (d:t) (a1:t) (b1:t) (c1:t) (d1:t) : GTot Type0 =
  let open FStar.UInt32 in
  let a' = a +%^ b in
  let d' = Spec.Lib.rotate_left (d ^^ a') 16ul in
  let c' = c +%^ d' in
  let b' = Spec.Lib.rotate_left (b ^^ c') 12ul in
  let a'' = a' +%^ b' in
  let d'' = Spec.Lib.rotate_left (d' ^^ a'') 8ul in
  let c'' = c' +%^ d'' in
  let b'' = Spec.Lib.rotate_left (b' ^^ c'') 7ul in
  a1 == a'' /\ b1 == b'' /\ c1 == c'' /\ d1 == d''


val line_: a:S.idx -> b:S.idx -> d:S.idx -> ss:UInt32.t {v ss > 0 /\ v ss < 32} -> s:state -> Tot (s':state{s' == S.line a b d ss s})
let line_ a b d s m =
  let open FStar.UInt32 in
  let m = upd m a (index m a +%^ index m b) in
  let m = upd m d (Spec.Lib.rotate_left (index m d ^^  index m a) s) in
  m


#reset-options "--max_fuel 0 --z3rlimit 500"

let new_line (s:state) (a:S.idx) (b:S.idx) (d:S.idx{a <> b /\ a <> d /\ b <> d}) (ss:UInt32.t{v ss > 0 /\ v ss < 32}) : Tot (s':state{
  let sa = index s a in let sb = index s b in let sd = index s d in
  let sa' = index s' a in let sb' = index s' b in let sd' = index s' d in
  let open FStar.UInt32 in
  let a' = sa +%^ sb in
  let d' = Spec.Lib.rotate_left (sd ^^ a') ss in
  sa' == a' /\ sd' == d'
  /\ (forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> a /\ i <> d) ==> index s' i == index s i)
  })
  = line_ a b d ss s


let quarter_round_standard
  (s:state) (a:S.idx) (b:S.idx) (c:S.idx) (d:S.idx{a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d}) :
  Tot (s':state{s' == S.quarter_round a b c d s}) =
  let s = new_line s a b d 16ul in
  let s = new_line s c d b 12ul in
  let s = new_line s a b d 8ul  in
  let s = new_line s c d b 7ul  in
  s


#reset-options "--max_fuel 0 --z3rlimit 500"

let lemma_quarter_round_standard
  (s:state) (a:S.idx) (b:S.idx) (c:S.idx) (d:S.idx{a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d}) :
  Lemma
  (let s' = quarter_round_standard s a b c d in
   let sa = index s a in let sb = index s b in let sc = index s c in let sd = index s d in
   let sa' = index s' a in let sb' = index s' b in let sc' = index s' c in let sd' = index s' d in
   lined sa sb sc sd sa' sb' sc' sd'
   /\ (forall (i:nat). {:pattern (Seq.index s' i)} (i < 16 /\ i <> a /\ i <> b /\ i <> c /\ i <> d
     ==> index s' i == index s i)))
   = ()


#reset-options "--max_fuel 0 --z3rlimit 1000"

let lemma_quarter_round_vectorized (s:vec_state) : Lemma
  (let s' = quarter_round_vec s in
   let s0 = index (index s 0) 0 in   let s1 = index (index s 0) 1 in
   let s2 = index (index s 0) 2 in   let s3 = index (index s 0) 3 in
   let s4 = index (index s 1) 0 in   let s5 = index (index s 1) 1 in
   let s6 = index (index s 1) 2 in   let s7 = index (index s 1) 3 in
   let s8 = index (index s 2) 0 in   let s9 = index (index s 2) 1 in
   let s10 = index (index s 2) 2 in  let s11 = index (index s 2) 3 in
   let s12 = index (index s 3) 0 in  let s13 = index (index s 3) 1 in
   let s14 = index (index s 3) 2 in  let s15 = index (index s 3) 3 in
   let s0' = index (index s' 0) 0 in   let s1' = index (index s' 0) 1 in
   let s2' = index (index s' 0) 2 in   let s3' = index (index s' 0) 3 in
   let s4' = index (index s' 1) 0 in   let s5' = index (index s' 1) 1 in
   let s6' = index (index s' 1) 2 in   let s7' = index (index s' 1) 3 in
   let s8' = index (index s' 2) 0 in   let s9' = index (index s' 2) 1 in
   let s10' = index (index s' 2) 2 in  let s11' = index (index s' 2) 3 in
   let s12' = index (index s' 3) 0 in  let s13' = index (index s' 3) 1 in
   let s14' = index (index s' 3) 2 in  let s15' = index (index s' 3) 3 in
   lined s0 s4 s8 s12 s0' s4' s8' s12'
   /\ lined s1 s5 s9 s13 s1' s5' s9' s13'
   /\ lined s2 s6 s10 s14 s2' s6' s10' s14'
   /\ lined s3 s7 s11 s15 s3' s7' s11' s15')
   = ()


#reset-options "--max_fuel 0 --z3rlimit 5"

val lemma_forall_elim: p:(nat -> Type) ->  q:(nat -> Type) -> j:nat{p j} ->
  Lemma (requires (forall (i:nat). p i ==> q i))
        (ensures (q j))
let lemma_forall_elim p q j = ()

val lemma_column_round_standard_1: s:state -> s':state -> Lemma
  (requires ((forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> 0 /\ i <> 4 /\ i <> 8 /\ i <> 12)  ==> index s' i == index s i)))
  (ensures (
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   s1 == s1' /\ s2 == s2' /\ s3 == s3'
   /\ s5 == s5' /\ s6 == s6' /\ s7 == s7'
   /\ s9 == s9' /\ s10 == s10' /\ s11 == s11'
   /\ s13 == s13' /\ s14 == s14' /\ s15 == s15'))
let lemma_column_round_standard_1 s s' =
  let p = fun (i:nat) -> (i < 16 /\ i <> 0 /\ i <> 4 /\ i <> 8 /\ i <> 12) in
  let q = fun (i:nat) -> (i < 16 /\ index s' i == index s i) in
  lemma_forall_elim p q 1;
  lemma_forall_elim p q 2;
  lemma_forall_elim p q 3;
  lemma_forall_elim p q 5;
  lemma_forall_elim p q 6;
  lemma_forall_elim p q 7;
  lemma_forall_elim p q 9;
  lemma_forall_elim p q 10;
  lemma_forall_elim p q 11;
  lemma_forall_elim p q 13;
  lemma_forall_elim p q 14;
  lemma_forall_elim p q 15


val column_round_standard_1: s:state -> Tot (s':state{
  (let s'' = S.quarter_round 0 4 8 12 s in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   lined s0 s4 s8 s12 s0' s4' s8' s12'
   /\ s'' == s'
   /\ s1 == s1' /\ s2 == s2' /\ s3 == s3'
   /\ s5 == s5' /\ s6 == s6' /\ s7 == s7'
   /\ s9 == s9' /\ s10 == s10' /\ s11 == s11'
   /\ s13 == s13' /\ s14 == s14' /\ s15 == s15')})
let column_round_standard_1 s =
  lemma_quarter_round_standard s 0 4 8 12;
  let s' = quarter_round_standard s 0 4 8 12 in
  cut (lined (index s 0) (index s 4) (index s 8) (index s 12) (index s' 0) (index s' 4) (index s' 8) (index s' 12));
  lemma_column_round_standard_1 s s';
  s'


val lemma_column_round_standard_2: s:state -> s':state -> Lemma
  (requires ((forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> 1 /\ i <> 5 /\ i <> 9 /\ i <> 13)  ==> index s' i == index s i)))
  (ensures (
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   s0 == s0' /\ s2 == s2' /\ s3 == s3'
   /\ s4 == s4' /\ s6 == s6' /\ s7 == s7'
   /\ s8 == s8' /\ s10 == s10' /\ s11 == s11'
   /\ s12 == s12' /\ s14 == s14' /\ s15 == s15'))
let lemma_column_round_standard_2 s s' =
  let p = fun (i:nat) -> (i < 16 /\ i <> 1 /\ i <> 5 /\ i <> 9 /\ i <> 13) in
  let q = fun (i:nat) -> (i < 16 /\ index s' i == index s i) in
  lemma_forall_elim p q 0;
  lemma_forall_elim p q 2;
  lemma_forall_elim p q 3;
  lemma_forall_elim p q 4;
  lemma_forall_elim p q 6;
  lemma_forall_elim p q 7;
  lemma_forall_elim p q 8;
  lemma_forall_elim p q 10;
  lemma_forall_elim p q 11;
  lemma_forall_elim p q 12;
  lemma_forall_elim p q 14;
  lemma_forall_elim p q 15


val column_round_standard_2: s:state -> Tot (s':state{
  (let s'' = S.quarter_round 0 4 8 12 s in
   let s'' = S.quarter_round 1 5 9 13 s'' in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   lined s0 s4 s8 s12 s0' s4' s8' s12'
   /\ s'' == s'
   /\ lined s1 s5 s9 s13 s1' s5' s9' s13'
   /\ s2 == s2' /\ s3 == s3'
   /\ s6 == s6' /\ s7 == s7'
   /\ s10 == s10' /\ s11 == s11'
   /\ s14 == s14' /\ s15 == s15')})
let column_round_standard_2 s =
  let s' = column_round_standard_1 s in
  lemma_quarter_round_standard s' 1 5 9 13;
  let s'' = quarter_round_standard s' 1 5 9 13 in
  lemma_column_round_standard_2 s' s'';
  s''


val lemma_column_round_standard_3: s:state -> s':state -> Lemma
  (requires ((forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> 2 /\ i <> 6 /\ i <> 10 /\ i <> 14)  ==> index s' i == index s i)))
  (ensures (
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   s0 == s0' /\ s1 == s1' /\ s3 == s3'
   /\ s4 == s4' /\ s5 == s5' /\ s7 == s7'
   /\ s8 == s8' /\ s9 == s9' /\ s11 == s11'
   /\ s12 == s12' /\ s13 == s13' /\ s15 == s15'))
let lemma_column_round_standard_3 s s' =
  let p = fun (i:nat) -> (i < 16 /\ i <> 2 /\ i <> 6 /\ i <> 10 /\ i <> 14) in
  let q = fun (i:nat) -> (i < 16 /\ index s' i == index s i) in
  lemma_forall_elim p q 0;
  lemma_forall_elim p q 1;
  lemma_forall_elim p q 3;
  lemma_forall_elim p q 4;
  lemma_forall_elim p q 5;
  lemma_forall_elim p q 7;
  lemma_forall_elim p q 8;
  lemma_forall_elim p q 9;
  lemma_forall_elim p q 11;
  lemma_forall_elim p q 12;
  lemma_forall_elim p q 13;
  lemma_forall_elim p q 15


val column_round_standard_3: s:state -> Tot (s':state{
  (let s'' = S.quarter_round 0 4 8 12 s in
   let s'' = S.quarter_round 1 5 9 13 s'' in
   let s'' = S.quarter_round 2 6 10 14 s'' in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   lined s0 s4 s8 s12 s0' s4' s8' s12'
   /\ lined s1 s5 s9 s13 s1' s5' s9' s13'
   /\ lined s2 s6 s10 s14 s2' s6' s10' s14'
   /\ s'' == s'
   /\ s3 == s3'
   /\ s7 == s7'
   /\ s11 == s11'
   /\ s15 == s15')})
let column_round_standard_3 s =
  let s'' = column_round_standard_2 s in
  lemma_quarter_round_standard s'' 2 6 10 14;
  let s''' = quarter_round_standard s'' 2 6 10 14 in
  lemma_column_round_standard_3 s'' s''';
  s'''


val lemma_column_round_standard_4: s:state -> s':state -> Lemma
  (requires ((forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> 3 /\ i <> 7 /\ i <> 11 /\ i <> 15)  ==> index s' i == index s i)))
  (ensures (
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   s0 == s0' /\ s1 == s1' /\ s2 == s2'
   /\ s4 == s4' /\ s5 == s5' /\ s6 == s6'
   /\ s8 == s8' /\ s9 == s9' /\ s10 == s10'
   /\ s12 == s12' /\ s13 == s13' /\ s14 == s14'))
let lemma_column_round_standard_4 s s' =
  let p = fun (i:nat) -> (i < 16 /\ i <> 3 /\ i <> 7 /\ i <> 11 /\ i <> 15) in
  let q = fun (i:nat) -> (i < 16 /\ index s' i == index s i) in
  lemma_forall_elim p q 0;
  lemma_forall_elim p q 1;
  lemma_forall_elim p q 2;
  lemma_forall_elim p q 4;
  lemma_forall_elim p q 5;
  lemma_forall_elim p q 6;
  lemma_forall_elim p q 8;
  lemma_forall_elim p q 9;
  lemma_forall_elim p q 10;
  lemma_forall_elim p q 12;
  lemma_forall_elim p q 13;
  lemma_forall_elim p q 14


#reset-options "--max_fuel 0"

val lemma_column_round_def: s:state -> Lemma
  (let s' = S.quarter_round 0 4 8 12 s in
   let s' = S.quarter_round 1 5 9 13 s' in
   let s' = S.quarter_round 2 6 10 14 s' in
   let s' = S.quarter_round 3 7 11 15 s' in
   s' == S.column_round s)
let lemma_column_round_def s = ()

val column_round_standard: s:state -> Tot (s':state{
  (s' == S.column_round s
   /\ (let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   lined s0 s4 s8 s12 s0' s4' s8' s12'
   /\ lined s1 s5 s9 s13 s1' s5' s9' s13'
   /\ lined s2 s6 s10 s14 s2' s6' s10' s14'
   /\ lined s3 s7 s11 s15 s3' s7' s11' s15'))})
let column_round_standard s =
  let s''' = column_round_standard_3 s in
  lemma_quarter_round_standard s''' 3 7 11 15;
  let s'''' = quarter_round_standard s''' 3 7 11 15 in
  lemma_column_round_standard_4 s''' s'''';
  lemma_column_round_def s;
  s''''


#reset-options "--max_fuel 0 --z3rlimit 100"

val shuffle_right: x:vec -> n:V.idx -> Tot (x':vec{
  index x' 0 == index x (n % 4)
  /\ index x' 1 == index x ((n+1) % 4)
  /\ index x' 2 == index x ((n+2) % 4)
  /\ index x' 3 == index x ((n+3) % 4)})
let shuffle_right x n =
  V.shuffle_right x n


#reset-options "--max_fuel 0 --z3rlimit 100"

val shuffle_rous_1: s:vec_state -> Tot (s':vec_state{
   let s0' = index (index s' 0) 0 in   let s1' = index (index s' 0) 1 in
   let s2' = index (index s' 0) 2 in   let s3' = index (index s' 0) 3 in
   let s4' = index (index s' 1) 0 in   let s5' = index (index s' 1) 1 in
   let s6' = index (index s' 1) 2 in   let s7' = index (index s' 1) 3 in
   let s8' = index (index s' 2) 0 in   let s9' = index (index s' 2) 1 in
   let s10' = index (index s' 2) 2 in  let s11' = index (index s' 2) 3 in
   let s12' = index (index s' 3) 0 in  let s13' = index (index s' 3) 1 in
   let s14' = index (index s' 3) 2 in  let s15' = index (index s' 3) 3 in
   let s0 = index (index s 0) 0 in   let s1 = index (index s 0) 1 in
   let s2 = index (index s 0) 2 in   let s3 = index (index s 0) 3 in
   let s4 = index (index s 1) 0 in   let s5 = index (index s 1) 1 in
   let s6 = index (index s 1) 2 in   let s7 = index (index s 1) 3 in
   let s8 = index (index s 2) 0 in   let s9 = index (index s 2) 1 in
   let s10 = index (index s 2) 2 in  let s11 = index (index s 2) 3 in
   let s12 = index (index s 3) 0 in  let s13 = index (index s 3) 1 in
   let s14 = index (index s 3) 2 in  let s15 = index (index s 3) 3 in
   s0 == s0' /\ s1 == s1' /\ s2 == s2' /\ s3 == s3'
   /\ s4' == s5 /\ s5' == s6 /\ s6' == s7 /\ s7' == s4
   /\ s8' == s10 /\ s9' == s11 /\ s10' == s8 /\ s11' == s9
   /\ s12' == s15 /\ s13' == s12 /\ s14' == s13 /\ s15' == s14
   /\ (let s'' = V.shuffle_row 1 1 s in
     let s'' = V.shuffle_row 2 2 s'' in
     let s'' = V.shuffle_row 3 3 s'' in
     s'' == s')
   })
let shuffle_rous_1 s =
  let s' = shuffle_row 1 1 s in
  lemma_eq_intro (shuffle_right (index s 1) 1) (index s' 1);
  lemma_eq_intro (index s 0) (index s' 0);
  lemma_eq_intro (index s 2) (index s' 2);
  lemma_eq_intro (index s 3) (index s' 3);
  let s'' = shuffle_row 2 2 s' in
  lemma_eq_intro (shuffle_right (index s' 2) 2) (index s'' 2);
  lemma_eq_intro (index s' 0) (index s'' 0);
  lemma_eq_intro (index s' 1) (index s'' 1);
  lemma_eq_intro (index s' 3) (index s'' 3);
  let s''' = shuffle_row 3 3 s'' in
  lemma_eq_intro (shuffle_right (index s'' 3) 3) (index s''' 3);
  lemma_eq_intro (index s'' 0) (index s''' 0);
  lemma_eq_intro (index s'' 1) (index s''' 1);
  lemma_eq_intro (index s'' 2) (index s''' 2);
  s'''


val shuffle_rous_2: s:vec_state -> Tot (s':vec_state{
   let s0' = index (index s' 0) 0 in   let s1' = index (index s' 0) 1 in
   let s2' = index (index s' 0) 2 in   let s3' = index (index s' 0) 3 in
   let s4' = index (index s' 1) 0 in   let s5' = index (index s' 1) 1 in
   let s6' = index (index s' 1) 2 in   let s7' = index (index s' 1) 3 in
   let s8' = index (index s' 2) 0 in   let s9' = index (index s' 2) 1 in
   let s10' = index (index s' 2) 2 in  let s11' = index (index s' 2) 3 in
   let s12' = index (index s' 3) 0 in  let s13' = index (index s' 3) 1 in
   let s14' = index (index s' 3) 2 in  let s15' = index (index s' 3) 3 in
   let s0 = index (index s 0) 0 in   let s1 = index (index s 0) 1 in
   let s2 = index (index s 0) 2 in   let s3 = index (index s 0) 3 in
   let s4 = index (index s 1) 0 in   let s5 = index (index s 1) 1 in
   let s6 = index (index s 1) 2 in   let s7 = index (index s 1) 3 in
   let s8 = index (index s 2) 0 in   let s9 = index (index s 2) 1 in
   let s10 = index (index s 2) 2 in  let s11 = index (index s 2) 3 in
   let s12 = index (index s 3) 0 in  let s13 = index (index s 3) 1 in
   let s14 = index (index s 3) 2 in  let s15 = index (index s 3) 3 in
   s0 == s0' /\ s1 == s1' /\ s2 == s2' /\ s3 == s3'
   /\ s4' == s7 /\ s5' == s4 /\ s6' == s5 /\ s7' == s6
   /\ s8' == s10 /\ s9' == s11 /\ s10' == s8 /\ s11' == s9
   /\ s12' == s13 /\ s13' == s14 /\ s14' == s15 /\ s15' == s12
   /\ (let s'' = V.shuffle_row 1 3 s in
     let s'' = V.shuffle_row 2 2 s'' in
     let s'' = V.shuffle_row 3 1 s'' in
     s'' == s')
   })
let shuffle_rous_2 s =
  let s' = shuffle_row 1 3 s in
  lemma_eq_intro (shuffle_right (index s 1) 3) (index s' 1);
  lemma_eq_intro (index s 0) (index s' 0);
  lemma_eq_intro (index s 2) (index s' 2);
  lemma_eq_intro (index s 3) (index s' 3);
  let s'' = shuffle_row 2 2 s' in
  lemma_eq_intro (shuffle_right (index s' 2) 2) (index s'' 2);
  lemma_eq_intro (index s' 0) (index s'' 0);
  lemma_eq_intro (index s' 1) (index s'' 1);
  lemma_eq_intro (index s' 3) (index s'' 3);
  let s''' = shuffle_row 3 1 s'' in
  lemma_eq_intro (shuffle_right (index s'' 3) 1) (index s''' 3);
  lemma_eq_intro (index s'' 0) (index s''' 0);
  lemma_eq_intro (index s'' 1) (index s''' 1);
  lemma_eq_intro (index s'' 2) (index s''' 2);
  s'''


#reset-options "--max_fuel 0 --z3rlimit 5"

val lemma_diagonal_round_standard_1: s:state -> s':state -> Lemma
  (requires ((forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> 0 /\ i <> 5 /\ i <> 10 /\ i <> 15)  ==> index s' i == index s i)))
  (ensures (
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   s1 == s1' /\ s2 == s2' /\ s3 == s3'
   /\ s4 == s4' /\ s6 == s6' /\ s7 == s7'
   /\ s9 == s9' /\ s8 == s8' /\ s11 == s11'
   /\ s13 == s13' /\ s14 == s14' /\ s12 == s12'))
let lemma_diagonal_round_standard_1 s s' =
  let p = fun (i:nat) -> (i < 16 /\ i <> 0 /\ i <> 5 /\ i <> 10 /\ i <> 15) in
  let q = fun (i:nat) -> (i < 16 /\ index s' i == index s i) in
  lemma_forall_elim p q 1;
  lemma_forall_elim p q 2;
  lemma_forall_elim p q 3;
  lemma_forall_elim p q 4;
  lemma_forall_elim p q 6;
  lemma_forall_elim p q 7;
  lemma_forall_elim p q 9;
  lemma_forall_elim p q 8;
  lemma_forall_elim p q 11;
  lemma_forall_elim p q 13;
  lemma_forall_elim p q 14;
  lemma_forall_elim p q 12


val diagonal_round_standard_1: s:state -> Tot (s':state{
  (let s'' = S.quarter_round 0 5 10 15 s in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   lined s0 s5 s10 s15 s0' s5' s10' s15'
   /\ s'' == s'
   /\ s1 == s1' /\ s2 == s2' /\ s3 == s3'
   /\ s4 == s4' /\ s6 == s6' /\ s7 == s7'
   /\ s9 == s9' /\ s8 == s8' /\ s11 == s11'
   /\ s13 == s13' /\ s14 == s14' /\ s12 == s12')})
let diagonal_round_standard_1 s =
  lemma_quarter_round_standard s 0 5 10 15;
  let s' = quarter_round_standard s 0 5 10 15 in
  cut (lined (index s 0) (index s 5) (index s 10) (index s 15) (index s' 0) (index s' 5) (index s' 10) (index s' 15));
  lemma_diagonal_round_standard_1 s s';
  s'


val lemma_diagonal_round_standard_2: s:state -> s':state -> Lemma
  (requires ((forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> 1 /\ i <> 6 /\ i <> 11 /\ i <> 12)  ==> index s' i == index s i)))
  (ensures (
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   s0 == s0' /\ s2 == s2' /\ s3 == s3'
   /\ s4 == s4' /\ s5 == s5' /\ s7 == s7'
   /\ s8 == s8' /\ s10 == s10' /\ s9 == s9'
   /\ s13 == s13' /\ s14 == s14' /\ s15 == s15'))
let lemma_diagonal_round_standard_2 s s' =
  let p = fun (i:nat) -> (i < 16 /\ i <> 1 /\ i <> 6 /\ i <> 11 /\ i <> 12) in
  let q = fun (i:nat) -> (i < 16 /\ index s' i == index s i) in
  lemma_forall_elim p q 0;
  lemma_forall_elim p q 2;
  lemma_forall_elim p q 3;
  lemma_forall_elim p q 4;
  lemma_forall_elim p q 5;
  lemma_forall_elim p q 7;
  lemma_forall_elim p q 8;
  lemma_forall_elim p q 10;
  lemma_forall_elim p q 9;
  lemma_forall_elim p q 13;
  lemma_forall_elim p q 14;
  lemma_forall_elim p q 15


val diagonal_round_standard_2: s:state -> Tot (s':state{
  (let s'' = S.quarter_round 0 5 10 15 s in
   let s'' = S.quarter_round 1 6 11 12 s'' in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   lined s0 s5 s10 s15 s0' s5' s10' s15'
   /\ s'' == s'
   /\ lined s1 s6 s11 s12 s1' s6' s11' s12'
   /\ s2 == s2' /\ s3 == s3'
   /\ s4 == s4' /\ s7 == s7'
   /\ s8 == s8' /\ s9 == s9'
   /\ s14 == s14' /\ s13 == s13')})
let diagonal_round_standard_2 s =
  let s' = diagonal_round_standard_1 s in
  lemma_quarter_round_standard s' 1 6 11 12;
  let s'' = quarter_round_standard s' 1 6 11 12 in
  lemma_diagonal_round_standard_2 s' s'';
  s''


val lemma_diagonal_round_standard_3: s:state -> s':state -> Lemma
  (requires ((forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> 2 /\ i <> 7 /\ i <> 8 /\ i <> 13)  ==> index s' i == index s i)))
  (ensures (
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   s0 == s0' /\ s1 == s1' /\ s3 == s3'
   /\ s4 == s4' /\ s5 == s5' /\ s6 == s6'
   /\ s10 == s10' /\ s9 == s9' /\ s11 == s11'
   /\ s12 == s12' /\ s14 == s14' /\ s15 == s15'))
let lemma_diagonal_round_standard_3 s s' =
  let p = fun (i:nat) -> (i < 16 /\ i <> 2 /\ i <> 7 /\ i <> 8 /\ i <> 13) in
  let q = fun (i:nat) -> (i < 16 /\ index s' i == index s i) in
  lemma_forall_elim p q 0;
  lemma_forall_elim p q 1;
  lemma_forall_elim p q 3;
  lemma_forall_elim p q 4;
  lemma_forall_elim p q 5;
  lemma_forall_elim p q 6;
  lemma_forall_elim p q 10;
  lemma_forall_elim p q 9;
  lemma_forall_elim p q 11;
  lemma_forall_elim p q 12;
  lemma_forall_elim p q 14;
  lemma_forall_elim p q 15


val diagonal_round_standard_3: s:state -> Tot (s':state{
  (let s'' = S.quarter_round 0 5 10 15 s in
   let s'' = S.quarter_round 1 6 11 12 s'' in
   let s'' = S.quarter_round 2 7  8 13 s'' in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   lined s0 s5 s10 s15 s0' s5' s10' s15'
   /\ lined s1 s6 s11 s12 s1' s6' s11' s12'
   /\ lined s2 s7 s8 s13 s2' s7' s8' s13'
   /\ s'' == s'
   /\ s3 == s3'
   /\ s4 == s4'
   /\ s9 == s9'
   /\ s14 == s14')})
let diagonal_round_standard_3 s =
  let s'' = diagonal_round_standard_2 s in
  lemma_quarter_round_standard s'' 2 7 8 13;
  let s''' = quarter_round_standard s'' 2 7 8 13 in
  lemma_diagonal_round_standard_3 s'' s''';
  s'''


val lemma_diagonal_round_standard_4: s:state -> s':state -> Lemma
  (requires ((forall (i:nat). {:pattern (index s' i)} (i < 16 /\ i <> 3 /\ i <> 4 /\ i <> 9 /\ i <> 14)  ==> index s' i == index s i)))
  (ensures (
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   s0 == s0' /\ s1 == s1' /\ s2 == s2'
   /\ s6 == s6' /\ s5 == s5' /\ s7 == s7'
   /\ s8 == s8' /\ s11 == s11' /\ s10 == s10'
   /\ s12 == s12' /\ s13 == s13' /\ s15 == s15'))
let lemma_diagonal_round_standard_4 s s' =
  let p = fun (i:nat) -> (i < 16 /\ i <> 3 /\ i <> 4 /\ i <> 9 /\ i <> 14) in
  let q = fun (i:nat) -> (i < 16 /\ index s' i == index s i) in
  lemma_forall_elim p q 0;
  lemma_forall_elim p q 1;
  lemma_forall_elim p q 2;
  lemma_forall_elim p q 7;
  lemma_forall_elim p q 5;
  lemma_forall_elim p q 6;
  lemma_forall_elim p q 8;
  lemma_forall_elim p q 11;
  lemma_forall_elim p q 10;
  lemma_forall_elim p q 12;
  lemma_forall_elim p q 13;
  lemma_forall_elim p q 15


#reset-options "--max_fuel 0 --z3rlimit 10"

val lemma_diagonal_round_def: s:state -> Lemma
  (let s' = S.quarter_round 0 5 10 15 s in
   let s' = S.quarter_round 1 6 11 12 s' in
   let s' = S.quarter_round 2 7 8  13 s' in
   let s' = S.quarter_round 3 4 9  14 s' in
   s' == S.diagonal_round s)
let lemma_diagonal_round_def s = ()

val diagonal_round_standard: s:state -> Tot (s':state{
  (s' == S.diagonal_round s
   /\ (let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   let s0' = index s' 0 in   let s1' = index s' 1 in
   let s2' = index s' 2 in   let s3' = index s' 3 in
   let s4' = index s' 4 in   let s5' = index s' 5 in
   let s6' = index s' 6 in   let s7' = index s' 7 in
   let s8' = index s' 8 in   let s9' = index s' 9 in
   let s10' = index s' 10 in  let s11' = index s' 11 in
   let s12' = index s' 12 in  let s13' = index s' 13 in
   let s14' = index s' 14 in  let s15' = index s' 15 in
   lined s0 s5 s10 s15 s0' s5' s10' s15'
   /\ lined s1 s6 s11 s12 s1' s6' s11' s12'
   /\ lined s2 s7 s8 s13 s2' s7' s8' s13'
   /\ lined s3 s4 s9 s14 s3' s4' s9' s14'))})
let diagonal_round_standard s =
  let s''' = diagonal_round_standard_3 s in
  lemma_quarter_round_standard s''' 3 4 9 14;
  let s'''' = quarter_round_standard s''' 3 4 9 14 in
  lemma_diagonal_round_standard_4 s''' s'''';
  lemma_diagonal_round_def s;
  s''''


val diagonal_round_vectorized: s:vec_state -> Tot (s':vec_state{
  (let s0 = index (index s 0) 0 in   let s1 = index (index s 0) 1 in
   let s2 = index (index s 0) 2 in   let s3 = index (index s 0) 3 in
   let s4 = index (index s 1) 0 in   let s5 = index (index s 1) 1 in
   let s6 = index (index s 1) 2 in   let s7 = index (index s 1) 3 in
   let s8 = index (index s 2) 0 in   let s9 = index (index s 2) 1 in
   let s10 = index (index s 2) 2 in  let s11 = index (index s 2) 3 in
   let s12 = index (index s 3) 0 in  let s13 = index (index s 3) 1 in
   let s14 = index (index s 3) 2 in  let s15 = index (index s 3) 3 in
   let s0' = index (index s' 0) 0 in   let s1' = index (index s' 0) 1 in
   let s2' = index (index s' 0) 2 in   let s3' = index (index s' 0) 3 in
   let s4' = index (index s' 1) 0 in   let s5' = index (index s' 1) 1 in
   let s6' = index (index s' 1) 2 in   let s7' = index (index s' 1) 3 in
   let s8' = index (index s' 2) 0 in   let s9' = index (index s' 2) 1 in
   let s10' = index (index s' 2) 2 in  let s11' = index (index s' 2) 3 in
   let s12' = index (index s' 3) 0 in  let s13' = index (index s' 3) 1 in
   let s14' = index (index s' 3) 2 in  let s15' = index (index s' 3) 3 in
   lined s0 s5 s10 s15 s0' s5' s10' s15'
   /\ lined s1 s6 s11 s12 s1' s6' s11' s12'
   /\ lined s2 s7 s8 s13 s2' s7' s8' s13'
   /\ lined s3 s4 s9 s14 s3' s4' s9' s14')})
let diagonal_round_vectorized s =
  let s' = shuffle_rous_1 s in
  lemma_quarter_round_vectorized s';
  let s'' = quarter_round_vec s' in
  let s''' = shuffle_rous_2 s'' in
  s'''


#reset-options "--max_fuel 0 --z3rlimit 100"


val lemma_quarter_round: s:vec_state -> Lemma
  (quarter_round_vec s == V.round s)
let lemma_quarter_round s = ()

val lemma_column_round: s:vec_state -> Lemma
  (quarter_round_vec s == V.column_round s)
let lemma_column_round s = ()

val lemma_shuffle_rows_1: s:vec_state -> Lemma
  (shuffle_rous_1 s == V.shuffle_rows_0123 s)
let lemma_shuffle_rows_1 s = ()

val lemma_shuffle_rows_2: s:vec_state -> Lemma
  (shuffle_rous_2 s == V.shuffle_rows_0321 s)
let lemma_shuffle_rows_2 s = ()

val lemma_diagonal_round_vec: s:vec_state -> Lemma
  (diagonal_round_vectorized s == V.diagonal_round s)
let lemma_diagonal_round_vec s =
  lemma_shuffle_rows_1 s;
  let s' = shuffle_rous_1 s in
  lemma_quarter_round s';
  let s'' = quarter_round_vec s' in
  lemma_shuffle_rows_2 s''

val double_round_vec: s:vec_state -> Tot vec_state
let double_round_vec s =
  let s' = quarter_round_vec s in
  let s'' = diagonal_round_vectorized s' in
  s''

val lemma_double_round_def: s:vec_state -> Lemma
  (double_round_vec s == V.double_round s)
let lemma_double_round_def s =
  lemma_column_round s;
  let s = quarter_round_vec s in
  lemma_diagonal_round_vec s

(* #reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100" *)

(* // TODO: move somewhere else *)
(* private val lemma_seq_of_list: (#a:Type) -> (l:list a) -> Lemma *)
(*   (forall (i:nat). {:pattern (Seq.index (Seq.seq_of_list l) i)} i < List.Tot.length l *)
(*              ==> Seq.index (Seq.seq_of_list l) i == List.Tot.index l i) *)
(* let rec lemma_seq_of_list #a l = *)
(*   match l with *)
(*   | [] -> Seq.lemma_eq_intro (Seq.seq_of_list l) Seq.createEmpty *)
(*   | hd::tl -> ( *)
(*     lemma_seq_of_list #a tl; *)
(*     Seq.lemma_eq_intro (Seq.seq_of_list l) (Seq.cons hd (Seq.seq_of_list tl)) *)
(*   ) *)

#reset-options "--max_fuel 0 --z3rlimit 100"

val lemma_setup_standard_1: k:S.key -> n:S.nonce -> c:S.counter -> Lemma
  (let s = S.setup k n c in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   s0 == 0x61707865ul /\ s1 == 0x3320646eul /\ s2 == 0x79622d32ul /\ s3 == 0x6b206574ul)
let lemma_setup_standard_1 k n c = ()

val lemma_setup_standard_2: k:S.key -> n:S.nonce -> c:S.counter -> Lemma
  (let s = S.setup k n c in
   let k = uint32s_from_le 8 k in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   s4 == index k 0 /\ s5 == index k 1 /\ s6 == index k 2 /\ s7 == index k 3
   /\ s8 == index k 4 /\ s9 == index k 5 /\ s10 == index k 6 /\ s11 == index k 7)
let lemma_setup_standard_2 k n c =
  lemma_eq_intro (slice (S.setup k n c) 4 12) (uint32s_from_le 8 k)


val lemma_setup_standard_3: k:S.key -> n:S.nonce -> c:S.counter -> Lemma
  (let s = S.setup k n c in
   let n = uint32s_from_le 3 n in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   s12 == UInt32.uint_to_t c /\ s13 == index n 0 /\ s14 == index n 1 /\ s15 == index n 2)
let lemma_setup_standard_3 k n c =
  lemma_eq_intro (slice (S.setup k n c) 12 13) (singleton (UInt32.uint_to_t c));
  lemma_eq_intro (slice (S.setup k n c) 13 16) (uint32s_from_le 3 n)


val lemma_setup_standard: k:S.key -> n:S.nonce -> c:S.counter -> Lemma
  (let s = S.setup k n c in
   let k = uint32s_from_le 8 k in
   let n = uint32s_from_le 3 n in
   let s0 = index s 0 in   let s1 = index s 1 in
   let s2 = index s 2 in   let s3 = index s 3 in
   let s4 = index s 4 in   let s5 = index s 5 in
   let s6 = index s 6 in   let s7 = index s 7 in
   let s8 = index s 8 in   let s9 = index s 9 in
   let s10 = index s 10 in  let s11 = index s 11 in
   let s12 = index s 12 in  let s13 = index s 13 in
   let s14 = index s 14 in  let s15 = index s 15 in
   s0 == 0x61707865ul /\ s1 == 0x3320646eul /\ s2 == 0x79622d32ul /\ s3 == 0x6b206574ul
   /\ s4 == index k 0 /\ s5 == index k 1 /\ s6 == index k 2 /\ s7 == index k 3
   /\ s8 == index k 4 /\ s9 == index k 5 /\ s10 == index k 6 /\ s11 == index k 7
   /\ s12 == UInt32.uint_to_t c /\ s13 == index n 0 /\ s14 == index n 1 /\ s15 == index n 2)
let lemma_setup_standard k n c =
  lemma_setup_standard_1 k n c;
  lemma_setup_standard_2 k n c;
  lemma_setup_standard_3 k n c


val lemma_setup_vec_1: k:V.key -> n:V.nonce -> c:V.counter -> Lemma
  (let s = V.setup k n c in
   let s0 = index (index s 0) 0 in   let s1 = index (index s 0) 1 in
   let s2 = index (index s 0) 2 in   let s3 = index (index s 0) 3 in
   let s4 = index (index s 1) 0 in   let s5 = index (index s 1) 1 in
   let s6 = index (index s 1) 2 in   let s7 = index (index s 1) 3 in
   let s8 = index (index s 2) 0 in   let s9 = index (index s 2) 1 in
   let s10 = index (index s 2) 2 in  let s11 = index (index s 2) 3 in
   let s12 = index (index s 3) 0 in  let s13 = index (index s 3) 1 in
   let s14 = index (index s 3) 2 in  let s15 = index (index s 3) 3 in
   s0 == 0x61707865ul /\ s1 == 0x3320646eul /\ s2 == 0x79622d32ul /\ s3 == 0x6b206574ul)
let lemma_setup_vec_1 k n c = ()


val lemma_setup_vec_2: k:S.key -> n:S.nonce -> c:S.counter -> Lemma
  (let s = V.setup k n c in
   let k = uint32s_from_le 8 k in
   let s4 = index (index s 1) 0 in   let s5 = index (index s 1) 1 in
   let s6 = index (index s 1) 2 in   let s7 = index (index s 1) 3 in
   let s8 = index (index s 2) 0 in   let s9 = index (index s 2) 1 in
   let s10 = index (index s 2) 2 in  let s11 = index (index s 2) 3 in
   s4 == index k 0 /\ s5 == index k 1 /\ s6 == index k 2 /\ s7 == index k 3
   /\ s8 == index k 4 /\ s9 == index k 5 /\ s10 == index k 6 /\ s11 == index k 7)
let lemma_setup_vec_2 k n c =
  lemma_uint32s_from_le_slice 8 k 4;
  let key_part_1:vec = uint32s_from_le 4 (Seq.slice k 0 16)  in
  let key_part_2:vec = uint32s_from_le 4 (Seq.slice k 16 32) in
  lemma_eq_intro (key_part_1 @| key_part_2) (uint32s_from_le 8 k);
  let nonce    :vec = Seq.cons (UInt32.uint_to_t c) (uint32s_from_le 3 n) in
  lemma_eq_intro (index (V.setup k n c) 1) (uint32s_from_le 4 (slice k 0 16));
  lemma_eq_intro (index (V.setup k n c) 2) (uint32s_from_le 4 (slice k 16 32))


val lemma_setup_vec_3: k:V.key -> n:V.nonce -> c:V.counter -> Lemma
  (let s = V.setup k n c in
   let n = uint32s_from_le 3 n in
   let s12 = index (index s 3) 0 in  let s13 = index (index s 3) 1 in
   let s14 = index (index s 3) 2 in  let s15 = index (index s 3) 3 in
   s12 == UInt32.uint_to_t c /\ s13 == index n 0 /\ s14 == index n 1 /\ s15 == index n 2)
let lemma_setup_vec_3 k n c =
  let nonce    :vec = Seq.cons (UInt32.uint_to_t c) (uint32s_from_le 3 n) in
  lemma_eq_intro (slice nonce 1 4) (uint32s_from_le 3 n)


val lemma_setup_vec: k:V.key -> n:V.nonce -> c:V.counter -> Lemma
  (let s = V.setup k n c in
   let k = uint32s_from_le 8 k in
   let n = uint32s_from_le 3 n in
   let s0 = index (index s 0) 0 in   let s1 = index (index s 0) 1 in
   let s2 = index (index s 0) 2 in   let s3 = index (index s 0) 3 in
   let s4 = index (index s 1) 0 in   let s5 = index (index s 1) 1 in
   let s6 = index (index s 1) 2 in   let s7 = index (index s 1) 3 in
   let s8 = index (index s 2) 0 in   let s9 = index (index s 2) 1 in
   let s10 = index (index s 2) 2 in  let s11 = index (index s 2) 3 in
   let s12 = index (index s 3) 0 in  let s13 = index (index s 3) 1 in
   let s14 = index (index s 3) 2 in  let s15 = index (index s 3) 3 in
   s0 == 0x61707865ul /\ s1 == 0x3320646eul /\ s2 == 0x79622d32ul /\ s3 == 0x6b206574ul
   /\ s4 == index k 0 /\ s5 == index k 1 /\ s6 == index k 2 /\ s7 == index k 3
   /\ s8 == index k 4 /\ s9 == index k 5 /\ s10 == index k 6 /\ s11 == index k 7
   /\ s12 == UInt32.uint_to_t c /\ s13 == index n 0 /\ s14 == index n 1 /\ s15 == index n 2)
let lemma_setup_vec k n c =
  lemma_setup_vec_1 k n c;
  lemma_setup_vec_2 k n c;
  lemma_setup_vec_3 k n c


val lemma_setup: k:S.key -> n:S.nonce -> c:S.counter -> Lemma
  (let sv = V.setup k n c in let s = S.setup k n c in
   eq_states' s sv)
let lemma_setup k n c =
  lemma_setup_standard k n c; lemma_setup_vec k n c


val lemma_iter_state: s:state -> sv:vec_state{eq_states' s sv} ->
  f:(state -> Tot state) -> fv:(vec_state -> Tot vec_state)  -> n:nat -> Lemma
  (requires (forall (s:state) (sv:vec_state). eq_states' s sv ==> eq_states' (f s) (fv sv)))
  (ensures (eq_states' (iter n f s) (iter n fv sv)))
  (decreases n)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let rec lemma_iter_state s sv f fv n =
  if n = 0 then ()
  else (
    lemma_iter_state (f s) (fv sv) f fv (n-1)
  )


#reset-options "--max_fuel 0 --z3rlimit 10"

val lemma_column_round_eq : s:state -> sv:vec_state{eq_states' s sv} -> Lemma
  (let s = S.column_round s in let sv = V.column_round sv in eq_states' s sv)
let lemma_column_round_eq s sv =
  cut (eq_states' s sv);
  let s' = column_round_standard s in
  lemma_column_round sv;
  let sv' = quarter_round_vec sv in
  let s0 = index s 0 in   let s1 = index s 1 in
  let s2 = index s 2 in   let s3 = index s 3 in
  let s4 = index s 4 in   let s5 = index s 5 in
  let s6 = index s 6 in   let s7 = index s 7 in
  let s8 = index s 8 in   let s9 = index s 9 in
  let s10 = index s 10 in  let s11 = index s 11 in
  let s12 = index s 12 in  let s13 = index s 13 in
  let s14 = index s 14 in  let s15 = index s 15 in
  let sv0 = index (index sv 0) 0 in   let sv1 = index (index sv 0) 1 in
  let sv2 = index (index sv 0) 2 in   let sv3 = index (index sv 0) 3 in
  let sv4 = index (index sv 1) 0 in   let sv5 = index (index sv 1) 1 in
  let sv6 = index (index sv 1) 2 in   let sv7 = index (index sv 1) 3 in
  let sv8 = index (index sv 2) 0 in   let sv9 = index (index sv 2) 1 in
  let sv10 = index (index sv 2) 2 in  let sv11 = index (index sv 2) 3 in
  let sv12 = index (index sv 3) 0 in  let sv13 = index (index sv 3) 1 in
  let sv14 = index (index sv 3) 2 in  let sv15 = index (index sv 3) 3 in
  cut (sv0 == s0); cut (sv1 == s1); cut (sv2 == s2); cut (sv3 == s3);
  cut (sv4 == s4); cut (sv5 == s5); cut (sv6 == s6); cut (sv7 == s7);
  cut (sv8 == s8); cut (sv9 == s9); cut (sv10 == s10); cut (sv11 == s11);
  cut (sv12 == s12); cut (sv13 == s13); cut (sv14 == s14); cut (sv15 == s15);
  let s0' = index s' 0 in   let s1' = index s' 1 in
  let s2' = index s' 2 in   let s3' = index s' 3 in
  let s4' = index s' 4 in   let s5' = index s' 5 in
  let s6' = index s' 6 in   let s7' = index s' 7 in
  let s8' = index s' 8 in   let s9' = index s' 9 in
  let s10' = index s' 10 in  let s11' = index s' 11 in
  let s12' = index s' 12 in  let s13' = index s' 13 in
  let s14' = index s' 14 in  let s15' = index s' 15 in
  let sv0' = index (index sv' 0) 0 in   let sv1' = index (index sv' 0) 1 in
  let sv2' = index (index sv' 0) 2 in   let sv3' = index (index sv' 0) 3 in
  let sv4' = index (index sv' 1) 0 in   let sv5' = index (index sv' 1) 1 in
  let sv6' = index (index sv' 1) 2 in   let sv7' = index (index sv' 1) 3 in
  let sv8' = index (index sv' 2) 0 in   let sv9' = index (index sv' 2) 1 in
  let sv10' = index (index sv' 2) 2 in  let sv11' = index (index sv' 2) 3 in
  let sv12' = index (index sv' 3) 0 in  let sv13' = index (index sv' 3) 1 in
  let sv14' = index (index sv' 3) 2 in  let sv15' = index (index sv' 3) 3 in
  cut (lined s0 s4 s8 s12 s0' s4' s8' s12');
  cut (lined s1 s5 s9 s13 s1' s5' s9' s13');
  cut (lined s2 s6 s10 s14 s2' s6' s10' s14');
  cut (lined s3 s7 s11 s15 s3' s7' s11' s15');
  lemma_quarter_round_vectorized sv;
  cut (lined sv0 sv4 sv8 sv12 sv0' sv4' sv8' sv12');
  cut (lined sv1 sv5 sv9 sv13 sv1' sv5' sv9' sv13');
  cut (lined sv2 sv6 sv10 sv14 sv2' sv6' sv10' sv14');
  cut (lined sv3 sv7 sv11 sv15 sv3' sv7' sv11' sv15');
  cut (sv' == V.column_round sv);
  cut (s' == S.column_round s)


val lemma_diagonal_round_eq : s:state -> sv:vec_state{eq_states' s sv} -> Lemma
  (let s = S.diagonal_round s in let sv = V.diagonal_round sv in eq_states' s sv)
let lemma_diagonal_round_eq s sv =
  cut (eq_states' s sv);
  let s' = diagonal_round_standard s in
  lemma_diagonal_round_vec sv;
  let sv' = diagonal_round_vectorized sv in
  let s0 = index s 0 in   let s1 = index s 1 in
  let s2 = index s 2 in   let s3 = index s 3 in
  let s4 = index s 4 in   let s5 = index s 5 in
  let s6 = index s 6 in   let s7 = index s 7 in
  let s8 = index s 8 in   let s9 = index s 9 in
  let s10 = index s 10 in  let s11 = index s 11 in
  let s12 = index s 12 in  let s13 = index s 13 in
  let s14 = index s 14 in  let s15 = index s 15 in
  let sv0 = index (index sv 0) 0 in   let sv1 = index (index sv 0) 1 in
  let sv2 = index (index sv 0) 2 in   let sv3 = index (index sv 0) 3 in
  let sv4 = index (index sv 1) 0 in   let sv5 = index (index sv 1) 1 in
  let sv6 = index (index sv 1) 2 in   let sv7 = index (index sv 1) 3 in
  let sv8 = index (index sv 2) 0 in   let sv9 = index (index sv 2) 1 in
  let sv10 = index (index sv 2) 2 in  let sv11 = index (index sv 2) 3 in
  let sv12 = index (index sv 3) 0 in  let sv13 = index (index sv 3) 1 in
  let sv14 = index (index sv 3) 2 in  let sv15 = index (index sv 3) 3 in
  cut (sv0 == s0); cut (sv1 == s1); cut (sv2 == s2); cut (sv3 == s3);
  cut (sv4 == s4); cut (sv5 == s5); cut (sv6 == s6); cut (sv7 == s7);
  cut (sv8 == s8); cut (sv9 == s9); cut (sv10 == s10); cut (sv11 == s11);
  cut (sv12 == s12); cut (sv13 == s13); cut (sv14 == s14); cut (sv15 == s15);
  let s0' = index s' 0 in   let s1' = index s' 1 in
  let s2' = index s' 2 in   let s3' = index s' 3 in
  let s4' = index s' 4 in   let s5' = index s' 5 in
  let s6' = index s' 6 in   let s7' = index s' 7 in
  let s8' = index s' 8 in   let s9' = index s' 9 in
  let s10' = index s' 10 in  let s11' = index s' 11 in
  let s12' = index s' 12 in  let s13' = index s' 13 in
  let s14' = index s' 14 in  let s15' = index s' 15 in
  let sv0' = index (index sv' 0) 0 in   let sv1' = index (index sv' 0) 1 in
  let sv2' = index (index sv' 0) 2 in   let sv3' = index (index sv' 0) 3 in
  let sv4' = index (index sv' 1) 0 in   let sv5' = index (index sv' 1) 1 in
  let sv6' = index (index sv' 1) 2 in   let sv7' = index (index sv' 1) 3 in
  let sv8' = index (index sv' 2) 0 in   let sv9' = index (index sv' 2) 1 in
  let sv10' = index (index sv' 2) 2 in  let sv11' = index (index sv' 2) 3 in
  let sv12' = index (index sv' 3) 0 in  let sv13' = index (index sv' 3) 1 in
  let sv14' = index (index sv' 3) 2 in  let sv15' = index (index sv' 3) 3 in
  cut (lined s0 s5 s10 s15 s0' s5' s10' s15');
  cut (lined s1 s6 s11 s12 s1' s6' s11' s12');
  cut (lined s2 s7 s8 s13 s2' s7' s8' s13');
  cut (lined s3 s4 s9 s14 s3' s4' s9' s14');
  cut (lined sv0 sv5 sv10 sv15 sv0' sv5' sv10' sv15');
  cut (lined sv1 sv6 sv11 sv12 sv1' sv6' sv11' sv12');
  cut (lined sv2 sv7 sv8 sv13 sv2' sv7' sv8' sv13');
  cut (lined sv3 sv4 sv9 sv14 sv3' sv4' sv9' sv14');
  cut (sv' == V.diagonal_round sv);
  cut (s' == S.diagonal_round s)


val lemma_double_round_eq: s:state -> sv:vec_state{eq_states' s sv} -> Lemma
  (let s = S.double_round s in let sv = V.double_round sv in eq_states' s sv)
let lemma_double_round_eq s sv =
  let s' = S.column_round s in
  let s'' = S.diagonal_round s' in
  cut (s'' == S.double_round s);
  let sv' = V.column_round sv in
  let sv'' = V.diagonal_round sv' in
  cut (sv'' == V.double_round sv);
  lemma_column_round_eq s sv;
  cut (eq_states' s' sv');
  lemma_diagonal_round_eq s' sv'


val lemma_double_round_eq_: s:state -> sv:vec_state -> Lemma
  (requires (eq_states' s sv))
  (ensures (let s = S.double_round s in let sv = V.double_round sv in eq_states' s sv))
let lemma_double_round_eq_ s sv = lemma_double_round_eq s sv

val lemma_double_round_eq': s:state -> sv:vec_state -> Lemma
  (eq_states' s sv ==> (let s = S.double_round s in let sv = V.double_round sv in eq_states' s sv))
let lemma_double_round_eq' s sv =
  Classical.move_requires (lemma_double_round_eq_ s) sv

val lemma_double_round_eq_forall_1: s:state -> Lemma
  (forall sv. eq_states' s sv ==> eq_states' (S.double_round s) (V.double_round sv))
let lemma_double_round_eq_forall_1 s =
  let post (sv:vec_state) =
    eq_states' s sv ==> eq_states' (S.double_round s) (V.double_round sv) in
  FStar.Classical.forall_intro #_ #post (lemma_double_round_eq' s)

val lemma_double_round_eq_forall: unit -> Lemma
  (forall s sv. eq_states' s sv ==> eq_states' (S.double_round s) (V.double_round sv))
let lemma_double_round_eq_forall () =
  let post (s:state) =
    (forall sv. eq_states' s sv ==> eq_states' (S.double_round s) (V.double_round sv)) in
  FStar.Classical.forall_intro #_ #post lemma_double_round_eq_forall_1

#reset-options "--max_fuel 0 --z3rlimit 5"

val lemma_chacha_rounds_vec: s:state -> sv:vec_state{eq_states' s sv} -> Lemma
  (let s' = S.rounds s in let sv' = V.rounds sv in
   eq_states' s' sv')
let lemma_chacha_rounds_vec s sv =
  lemma_double_round_eq_forall ();
  lemma_iter_state s sv S.double_round V.double_round 10;
  cut (eq_states' (iter 10 S.double_round s) (iter 10 V.double_round sv));
  cut (S.rounds s == iter 10 S.double_round s);
  cut (V.rounds sv == iter 10 V.double_round sv)


val lemma_chacha_core_std: s:state -> s':state -> Lemma
  (let s'' = Spec.Loops.seq_map2 FStar.UInt32.op_Plus_Percent_Hat s' s in
  let s0 = index s 0 in   let s1 = index s 1 in
  let s2 = index s 2 in   let s3 = index s 3 in
  let s4 = index s 4 in   let s5 = index s 5 in
  let s6 = index s 6 in   let s7 = index s 7 in
  let s8 = index s 8 in   let s9 = index s 9 in
  let s10 = index s 10 in  let s11 = index s 11 in
  let s12 = index s 12 in  let s13 = index s 13 in
  let s14 = index s 14 in  let s15 = index s 15 in
  let s0' = index s' 0 in   let s1' = index s' 1 in
  let s2' = index s' 2 in   let s3' = index s' 3 in
  let s4' = index s' 4 in   let s5' = index s' 5 in
  let s6' = index s' 6 in   let s7' = index s' 7 in
  let s8' = index s' 8 in   let s9' = index s' 9 in
  let s10' = index s' 10 in  let s11' = index s' 11 in
  let s12' = index s' 12 in  let s13' = index s' 13 in
  let s14' = index s' 14 in  let s15' = index s' 15 in
  let s0'' = index s'' 0 in   let s1'' = index s'' 1 in
  let s2'' = index s'' 2 in   let s3'' = index s'' 3 in
  let s4'' = index s'' 4 in   let s5'' = index s'' 5 in
  let s6'' = index s'' 6 in   let s7'' = index s'' 7 in
  let s8'' = index s'' 8 in   let s9'' = index s'' 9 in
  let s10'' = index s'' 10 in  let s11'' = index s'' 11 in
  let s12'' = index s'' 12 in  let s13'' = index s'' 13 in
  let s14'' = index s'' 14 in  let s15'' = index s'' 15 in
  FStar.UInt32.(
  s0'' == s0' +%^ s0
  /\ s1'' == s1' +%^ s1
  /\ s2'' == s2' +%^ s2
  /\ s3'' == s3' +%^ s3
  /\ s4'' == s4' +%^ s4
  /\ s5'' == s5' +%^ s5
  /\ s6'' == s6' +%^ s6
  /\ s7'' == s7' +%^ s7
  /\ s8'' == s8' +%^ s8
  /\ s9'' == s9' +%^ s9
  /\ s10'' == s10' +%^ s10
  /\ s11'' == s11' +%^ s11
  /\ s12'' == s12' +%^ s12
  /\ s13'' == s13' +%^ s13
  /\ s14'' == s14' +%^ s14
  /\ s15'' == s15' +%^ s15))
#reset-options "--max_fuel 0 --z3rlimit 100"
let lemma_chacha_core_std s s' = ()

val lemma_chacha_core_vec: s:vec_state -> s':vec_state -> Lemma
  (let s'' = Spec.Loops.seq_map2 V.op_Plus_Percent_Hat s' s in
  let s0 = index (index s 0) 0 in   let s1 = index (index s 0) 1 in
  let s2 = index (index s 0) 2 in   let s3 = index (index s 0) 3 in
  let s4 = index (index s 1) 0 in   let s5 = index (index s 1) 1 in
  let s6 = index (index s 1) 2 in   let s7 = index (index s 1) 3 in
  let s8 = index (index s 2) 0 in   let s9 = index (index s 2) 1 in
  let s10 = index (index s 2) 2 in  let s11 = index (index s 2) 3 in
  let s12 = index (index s 3) 0 in  let s13 = index (index s 3) 1 in
  let s14 = index (index s 3) 2 in  let s15 = index (index s 3) 3 in
  let s0' = index (index s' 0) 0 in   let s1' = index (index s' 0) 1 in
  let s2' = index (index s' 0) 2 in   let s3' = index (index s' 0) 3 in
  let s4' = index (index s' 1) 0 in   let s5' = index (index s' 1) 1 in
  let s6' = index (index s' 1) 2 in   let s7' = index (index s' 1) 3 in
  let s8' = index (index s' 2) 0 in   let s9' = index (index s' 2) 1 in
  let s10' = index (index s' 2) 2 in  let s11' = index (index s' 2) 3 in
  let s12' = index (index s' 3) 0 in  let s13' = index (index s' 3) 1 in
  let s14' = index (index s' 3) 2 in  let s15' = index (index s' 3) 3 in
  let s0'' = index (index s'' 0) 0 in   let s1'' = index (index s'' 0) 1 in
  let s2'' = index (index s'' 0) 2 in   let s3'' = index (index s'' 0) 3 in
  let s4'' = index (index s'' 1) 0 in   let s5'' = index (index s'' 1) 1 in
  let s6'' = index (index s'' 1) 2 in   let s7'' = index (index s'' 1) 3 in
  let s8'' = index (index s'' 2) 0 in   let s9'' = index (index s'' 2) 1 in
  let s10'' = index (index s'' 2) 2 in  let s11'' = index (index s'' 2) 3 in
  let s12'' = index (index s'' 3) 0 in  let s13'' = index (index s'' 3) 1 in
  let s14'' = index (index s'' 3) 2 in  let s15'' = index (index s'' 3) 3 in
  FStar.UInt32.(
  s0'' == s0' +%^ s0
  /\ s1'' == s1' +%^ s1
  /\ s2'' == s2' +%^ s2
  /\ s3'' == s3' +%^ s3
  /\ s4'' == s4' +%^ s4
  /\ s5'' == s5' +%^ s5
  /\ s6'' == s6' +%^ s6
  /\ s7'' == s7' +%^ s7
  /\ s8'' == s8' +%^ s8
  /\ s9'' == s9' +%^ s9
  /\ s10'' == s10' +%^ s10
  /\ s11'' == s11' +%^ s11
  /\ s12'' == s12' +%^ s12
  /\ s13'' == s13' +%^ s13
  /\ s14'' == s14' +%^ s14
  /\ s15'' == s15' +%^ s15))
#reset-options "--max_fuel 0 --z3rlimit 100"
let lemma_chacha_core_vec s s' = ()

val lemma_chacha_core: s:state -> sv:vec_state{eq_states' s sv} -> Lemma
  (let s = S.chacha20_core s in let sv = V.chacha20_core sv in
   eq_states' s sv)
let lemma_chacha_core s sv =
  lemma_chacha_rounds_vec s sv;
  let s' = S.rounds s in
  let sv' = V.rounds sv in
  lemma_chacha_core_std s s'; lemma_chacha_core_vec sv sv'


private let lemma_append_assoc (#a:Type) (x:seq a) (y:seq a) (z:seq a) : Lemma
  (x @| (y @| z) == (x @| y) @| z) = lemma_eq_intro ((x @| y) @| z) (x @| (y @| z))


val lemma_chacha_block_slice: s:state -> Lemma
  (uint32s_to_le 16 s == uint32s_to_le 4 (slice s 0 4)
                         @| uint32s_to_le 4 (slice s 4  8)
                         @| uint32s_to_le 4 (slice s 8  12)
                         @| uint32s_to_le 4 (slice s 12 16))
#reset-options "--max_fuel 0 --z3rlimit 100"
let lemma_chacha_block_slice b =
  lemma_uint32s_to_le_slice 16 b 8;
  let b0 = slice b 0 8 in
  let b1 = slice b 8 16 in
  cut (uint32s_to_le 16 b == uint32s_to_le 8 b0 @| uint32s_to_le 8 b1);
  lemma_uint32s_to_le_slice 8 b0 4;
  lemma_uint32s_to_le_slice 8 b1 4;
  cut (uint32s_to_le 8 b0 == uint32s_to_le 4 (slice b0 0 4) @| uint32s_to_le 4 (slice b0 4 8));
  cut (uint32s_to_le 8 b1 == uint32s_to_le 4 (slice b1 0 4) @| uint32s_to_le 4 (slice b1 4 8));
  lemma_eq_intro (slice b0 0 4) (slice b 0 4);
  lemma_eq_intro (slice b0 4 8) (slice b 4 8);
  lemma_eq_intro (slice b1 0 4) (slice b 8 12);
  lemma_eq_intro (slice b1 4 8) (slice b 12 16);
  cut (uint32s_to_le 8 b0 == uint32s_to_le 4 (slice b 0 4) @| uint32s_to_le 4 (slice b 4 8));
  cut (uint32s_to_le 8 b1 == uint32s_to_le 4 (slice b 8 12) @| uint32s_to_le 4 (slice b 12 16));
  cut (uint32s_to_le 16 b == (uint32s_to_le 4 (slice b 0 4) @| uint32s_to_le 4 (slice b 4 8))
                             @| (uint32s_to_le 4 (slice b 8 12) @| uint32s_to_le 4 (slice b 12 16)));
  lemma_append_assoc (uint32s_to_le 4 (slice b 0 4) @| uint32s_to_le 4 (slice b 4 8))
                     (uint32s_to_le 4 (slice b 8 12)) (uint32s_to_le 4 (slice b 12 16));
  lemma_append_assoc (uint32s_to_le 4 (slice b 0 4)) (uint32s_to_le 4 (slice b 4 8))
                     (uint32s_to_le 4 (slice b 8 12) @| uint32s_to_le 4 (slice b 12 16))


val lemma_chacha20_block: k:key -> n:nonce -> c:counter ->
  Lemma (let b = S.chacha20_block k n c in let b' = V.chacha20_block k n c in  b == b')
let lemma_chacha20_block k n c =
  lemma_setup k n c;
  let s = S.setup k n c in
  let sv = V.setup k n c in
  cut (eq_states' s sv);
  lemma_chacha_core s sv;
  let s' = S.chacha20_core s in
  let sv' = V.chacha20_core sv in
  lemma_chacha_block_slice s';
  lemma_eq_states_intro s' sv';
  lemma_eq_intro (index sv' 0) (slice s' 0 4);
  lemma_eq_intro (index sv' 1) (slice s' 4 8);
  lemma_eq_intro (index sv' 2) (slice s' 8 12);
  lemma_eq_intro (index sv' 3) (slice s' 12 16);
  lemma_eq_intro (uint32s_to_le 4 (index sv' 0) @|  uint32s_to_le 4 (index sv' 1) @|  uint32s_to_le 4 (index sv' 2) @|  uint32s_to_le 4 (index sv' 3)) (uint32s_to_le 16 s')


val lemma_chacha20_counter_mode_blocks: k:key -> n:nonce -> c:counter -> m:bytes{c + 1 * (length m / 64) < pow2 32 /\
    length m % (64 * 1) = 0} -> Lemma
  (requires (True))
  (ensures (Spec.CTR.counter_mode_blocks S.chacha20_ctx S.chacha20_cipher k n c m ==
            Spec.CTR.counter_mode_blocks V.chacha20_ctx V.chacha20_cipher k n c m))
  (decreases (length m))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"
let rec lemma_chacha20_counter_mode_blocks k n c m =
  if length m = 0 then ()
  else (
    let len = length m in
    let len' = len / (64 * 1) in
    Math.Lemmas.lemma_div_mod len (64 * 1);
    let prefix, block = split m (len - 64 * 1) in    
      (* TODO: move to a single lemma for clarify *)
      Math.Lemmas.lemma_mod_plus (length prefix) 1 (64 * 1);
      Math.Lemmas.lemma_div_le (length prefix) len 64;
      Spec.CTR.Lemmas.lemma_div len (64 * 1);
      (* End TODO *)
    lemma_chacha20_counter_mode_blocks k n c prefix;
    lemma_chacha20_block k n ((c + (len / 64 - 1)) * 1)
  )
  

val lemma_chacha20_encrypt_bytes: k:key -> n:nonce -> c:counter -> m:bytes{c + length m / 64 < pow2 32} -> Lemma
  (requires (True))
  (ensures (V.chacha20_encrypt_bytes k n c m == S.chacha20_encrypt_bytes k n c m))
  (decreases (length m))
#reset-options "--max_fuel 0 --z3rlimit 100"
let rec lemma_chacha20_encrypt_bytes k n c m =
  let len = length m in
  let blocks_len = (1 * 64) * (len / (64 * 1)) in
  let part_len   = len % (64 * 1) in
  Math.Lemmas.lemma_div_mod len (64 * 1);
  Math.Lemmas.multiple_modulo_lemma (len / (64 * 1)) (64 * 1);
  Math.Lemmas.lemma_div_le (blocks_len) len 64;
  let blocks, last_block = split m blocks_len in
  lemma_chacha20_counter_mode_blocks k n c blocks;
  if part_len > 0
  then
    lemma_chacha20_block k n (c+1*(length m / 64))
  else ()
