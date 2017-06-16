//
//   Copyright 2016-2017  INRIA
//
//   Maintainers: Jean-Karim Zinzindohoué
//                Karthikeyan Bhargavan
//                Benjamin Beurdouche
//
//   Licensed under the Apache License, Version 2.0 (the "License");
//   you may not use this file except in compliance with the License.
//   You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS,
//   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//   See the License for the specific language governing permissions and
//   limitations under the License.
//

module Spec.Chacha20_vec256.Lemmas

open FStar.Mul
open FStar.Seq
open Seq.Lib

module V1 = Spec.Chacha20_vec
module V2 = Spec.Chacha20_vec256
module U32 = FStar.UInt32

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

val get_fst: V2.vec -> Tot V1.vec
let get_fst v = slice v 0 4

val get_snd: V2.vec -> Tot V1.vec
let get_snd v =
  cut (length v = 8);
  slice v 4 8


val get_st1: V2.state -> Tot V1.state
let get_st1 st =
  let s0:V2.vec = index st 0 in
  let s1:V2.vec = index st 1 in
  let s2:V2.vec = index st 2 in
  let s3:V2.vec = index st 3 in
  let v0 = get_fst s0 in
  let v1 = get_fst s1 in
  let v2 = get_fst s2 in
  let v3 = get_fst s3 in
  seq_4 v0 v1 v2 v3


val get_st2: V2.state -> Tot V1.state
let get_st2 st =
  let s0:V2.vec = index st 0 in
  let s1:V2.vec = index st 1 in
  let s2:V2.vec = index st 2 in
  let s3:V2.vec = index st 3 in
  let v0 = get_snd s0 in
  let v1 = get_snd s1 in
  let v2 = get_snd s2 in
  let v3 = get_snd s3 in
  seq_4 v0 v1 v2 v3


val mk_st: st1:V1.state -> st2:V1.state -> Tot V2.state
let mk_st st1 st2 =
  let v10 = index st1 0 in
  let v11 = index st1 1 in
  let v12 = index st1 2 in
  let v13 = index st1 3 in
  let v20 = index st2 0 in
  let v21 = index st2 1 in
  let v22 = index st2 2 in
  let v23 = index st2 3 in
  let s0:V2.vec = v10 @| v20 in
  let s1:V2.vec = v11 @| v21 in
  let s2:V2.vec = v12 @| v22 in
  let s3:V2.vec = v13 @| v23 in
  seq_4 s0 s1 s2 s3

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_vec_get: st:V2.vec -> Lemma (get_fst st @| get_snd st == st)
let lemma_vec_get st =
  lemma_slice048 st

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

val lemma_mk_state: st:V2.state -> Lemma (mk_st (get_st1 st) (get_st2 st) = st)
let lemma_mk_state st =
  let st1 = get_st1 st in let st2 = get_st2 st in
  lemma_vec_get (index st 0);
  lemma_vec_get (index st 1);
  lemma_vec_get (index st 2);
  lemma_vec_get (index st 3);
  lemma_eq_intro st (mk_st st1 st2)

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val lemma_shuffle_right_fst: v:V2.vec -> n:V2.idx ->
  Lemma (get_fst (V2.shuffle_right v n) == V1.shuffle_right (get_fst v) n)
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let lemma_shuffle_right_fst v n =
  lemma_eq_intro (get_fst (V2.shuffle_right v n)) (V1.shuffle_right (get_fst v) n)


val lemma_shuffle_right_fst: v:V2.vec -> n:V2.idx ->
  Lemma (get_fst (V2.shuffle_right v n) == V1.shuffle_right (get_fst v) n)
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let lemma_shuffle_right_fst v n =
  lemma_eq_intro (get_fst (V2.shuffle_right v n)) (V1.shuffle_right (get_fst v) n)


val lemma_shuffle_right_snd: v:V2.vec -> n:V2.idx ->
  Lemma (get_snd (V2.shuffle_right v n) == V1.shuffle_right (get_snd v) n)
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let lemma_shuffle_right_snd v n =
  lemma_eq_intro (get_snd (V2.shuffle_right v n)) (V1.shuffle_right (get_snd v) n)


val lemma_shuffle_right: v:V2.vec -> n:V2.idx ->
  Lemma (get_fst (V2.shuffle_right v n) == V1.shuffle_right (get_fst v) n /\
    get_snd (V2.shuffle_right v n) == V1.shuffle_right (get_snd v) n)
let lemma_shuffle_right v n =
  lemma_shuffle_right_fst v n;
  lemma_shuffle_right_snd v n


val lemma_shuffle_row11: s:V2.state -> n:V2.idx -> Lemma
  (get_st1 (V2.shuffle_row 1 n s) == V1.shuffle_row 1 n (get_st1 s))
let lemma_shuffle_row11 s n =
  let st1 = get_st1 s in
  let s'  = V2.shuffle_row 1 n s in
  let st1' = V1.shuffle_row 1 n st1 in
  cut (s' == upd s 1 (V2.shuffle_right (index s 1) n));
  cut (st1' == upd st1 1 (V1.shuffle_right (index st1 1) n));
  lemma_upd_1 s (V2.shuffle_right (index s 1) n);
  lemma_upd_1 st1 (V1.shuffle_right (index st1 1) n);
  lemma_eq_intro (get_st1 s') (st1')

val lemma_shuffle_row12: s:V2.state -> n:V2.idx -> Lemma
  (get_st1 (V2.shuffle_row 2 n s) == V1.shuffle_row 2 n (get_st1 s))
let lemma_shuffle_row12 s n =
  let st1 = get_st1 s in
  let s'  = V2.shuffle_row 2 n s in
  let st1' = V1.shuffle_row 2 n st1 in
  cut (s' == upd s 2 (V2.shuffle_right (index s 2) n));
  cut (st1' == upd st1 2 (V1.shuffle_right (index st1 2) n));
  lemma_upd_2 s (V2.shuffle_right (index s 2) n);
  lemma_upd_2 st1 (V1.shuffle_right (index st1 2) n);
  lemma_eq_intro (get_st1 s') (st1')

val lemma_shuffle_row13: s:V2.state -> n:V2.idx -> Lemma
  (get_st1 (V2.shuffle_row 3 n s) == V1.shuffle_row 3 n (get_st1 s))
let lemma_shuffle_row13 s n =
  let st1 = get_st1 s in
  let s'  = V2.shuffle_row 3 n s in
  let st1' = V1.shuffle_row 3 n st1 in
  cut (s' == upd s 3 (V2.shuffle_right (index s 3) n));
  cut (st1' == upd st1 3 (V1.shuffle_right (index st1 3) n));
  lemma_upd_3 s (V2.shuffle_right (index s 3) n);
  lemma_upd_3 st1 (V1.shuffle_right (index st1 3) n);
  lemma_eq_intro (get_st1 s') (st1')

val lemma_shuffle_row21: s:V2.state -> n:V2.idx -> Lemma
  (get_st2 (V2.shuffle_row 1 n s) == V1.shuffle_row 1 n (get_st2 s))
let lemma_shuffle_row21 s n =
  let st2 = get_st2 s in
  lemma_shuffle_right (index s 1) n;
  let s'  = V2.shuffle_row 1 n s in
  let st2' = V1.shuffle_row 1 n st2 in
  cut (s' == upd s 1 (V2.shuffle_right (index s 1) n));
  cut (st2' == upd st2 1 (V1.shuffle_right (index st2 1) n));
  lemma_upd_1 s (V2.shuffle_right (index s 1) n);
  lemma_upd_1 st2 (V1.shuffle_right (index st2 1) n);
  lemma_eq_intro (get_st2 s') (st2')

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 200"

val lemma_shuffle_row22: s:V2.state -> n:V2.idx -> Lemma
  (get_st2 (V2.shuffle_row 2 n s) == V1.shuffle_row 2 n (get_st2 s))
let lemma_shuffle_row22 s n =
  let st2 = get_st2 s in
  lemma_shuffle_right (index s 2) n;
  let s'  = V2.shuffle_row 2 n s in
  let st2' = V1.shuffle_row 2 n st2 in
  cut (s' == upd s 2 (V2.shuffle_right (index s 2) n));
  cut (st2' == upd st2 2 (V1.shuffle_right (index st2 2) n));
  lemma_upd_2 s (V2.shuffle_right (index s 2) n);
  lemma_upd_2 st2 (V1.shuffle_right (index st2 2) n);
  lemma_eq_intro (get_st2 s') (st2')

val lemma_shuffle_row23: s:V2.state -> n:V2.idx -> Lemma
  (get_st2 (V2.shuffle_row 3 n s) == V1.shuffle_row 3 n (get_st2 s))
let lemma_shuffle_row23 s n =
  let st2 = get_st2 s in
  lemma_shuffle_right (index s 3) n;
  let s'  = V2.shuffle_row 3 n s in
  let st2' = V1.shuffle_row 3 n st2 in
  cut (s' == upd s 3 (V2.shuffle_right (index s 3) n));
  cut (st2' == upd st2 3 (V1.shuffle_right (index st2 3) n));
  lemma_upd_3 s (V2.shuffle_right (index s 3) n);
  lemma_upd_3 st2 (V1.shuffle_right (index st2 3) n);
  lemma_eq_intro (get_st2 s') (st2')

val lemma_shuffle_row0123_1: s:V2.state -> Lemma
  (get_st1 (V2.shuffle_rows_0123 s) == V1.shuffle_rows_0123 (get_st1 s))
let lemma_shuffle_row0123_1 s =
  lemma_shuffle_row11 s 1;
  let s = V2.shuffle_row 1 1 s in
  lemma_shuffle_row12 s 2;
  let s = V2.shuffle_row 2 2 s in
  lemma_shuffle_row13 s 3

val lemma_shuffle_row0123_2: s:V2.state -> Lemma
  (get_st2 (V2.shuffle_rows_0123 s) == V1.shuffle_rows_0123 (get_st2 s))
let lemma_shuffle_row0123_2 s =
  lemma_shuffle_row21 s 1;
  let s = V2.shuffle_row 1 1 s in
  lemma_shuffle_row22 s 2;
  let s = V2.shuffle_row 2 2 s in
  lemma_shuffle_row23 s 3

val lemma_shuffle_row0321_1: s:V2.state -> Lemma
  (get_st1 (V2.shuffle_rows_0321 s) == V1.shuffle_rows_0321 (get_st1 s))
let lemma_shuffle_row0321_1 s =
  lemma_shuffle_row11 s 3;
  let s = V2.shuffle_row 1 3 s in
  lemma_shuffle_row12 s 2;
  let s = V2.shuffle_row 2 2 s in
  lemma_shuffle_row13 s 1

val lemma_shuffle_row0321_2: s:V2.state -> Lemma
  (get_st2 (V2.shuffle_rows_0321 s) == V1.shuffle_rows_0321 (get_st2 s))
let lemma_shuffle_row0321_2 s =
  lemma_shuffle_row21 s 3;
  let s = V2.shuffle_row 1 3 s in
  lemma_shuffle_row22 s 2;
  let s = V2.shuffle_row 2 2 s in
  lemma_shuffle_row23 s 1

val lemma_shuffle_row0123: s:V2.state -> Lemma
  (get_st1 (V2.shuffle_rows_0123 s) == V1.shuffle_rows_0123 (get_st1 s)
  /\ get_st2 (V2.shuffle_rows_0123 s) == V1.shuffle_rows_0123 (get_st2 s))
let lemma_shuffle_row0123 s =
  lemma_shuffle_row0123_1 s;
  lemma_shuffle_row0123_2 s


val lemma_shuffle_row0321: s:V2.state -> Lemma
  (get_st1 (V2.shuffle_rows_0321 s) == V1.shuffle_rows_0321 (get_st1 s)
  /\ get_st2 (V2.shuffle_rows_0321 s) == V1.shuffle_rows_0321 (get_st2 s))
let lemma_shuffle_row0321 s =
  lemma_shuffle_row0321_1 s;
  lemma_shuffle_row0321_2 s

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 500"


(* val lemma_line_03_1_: m:V1.state -> s:UInt32.t{UInt32.v s < 32} -> Lemma *)
(*   (let mm = m in *)
(*    let m = upd m 0 V1.(index m 0 +%^ index m 1) in *)
(*    let m = upd m 3 V1.((index m 3 ^^  index m 0) <<< s) in *)
(*    m == V1.line 0 1 3 s mm) *)
(* let lemma_line_03_1_ st s = () *)


val lemma_line_03_1: st:V2.state -> s:UInt32.t{UInt32.v s < 32} -> Lemma
   (get_st1 (V2.line 0 1 3 s st) == V1.line 0 1 3 s (get_st1 st))
let lemma_line_03_1 st s =
  let s1 = get_st1 st in
  let x = (V2.(index st 0 +%^ index st 1)) in
  let y = (V1.(index s1 0 +%^ index s1 1)) in
  lemma_eq_intro (get_fst x) y;
  let st' = upd st 0 x in
  let s1' = upd s1 0 y in
  lemma_upd_0 st x;
  lemma_upd_0 s1 y;
  lemma_eq_intro (get_st1 st') (s1');
  let x = V2.((index st' 3 ^^ index st' 0) <<< s) in
  let y = V1.((index s1' 3 ^^ index s1' 0) <<< s) in
  lemma_eq_intro (get_fst x) y;
  let st'' = upd st' 3 x in
  let s1'' = upd s1' 3 y in
  lemma_upd_3 st' x;
  lemma_upd_3 s1' y;
  lemma_eq_intro (get_st1 st'') (s1'')


val lemma_line_21_1: st:V2.state -> s:UInt32.t{UInt32.v s < 32} -> Lemma
   (get_st1 (V2.line 2 3 1 s st) == V1.line 2 3 1 s (get_st1 st))
let lemma_line_21_1 st s =
  let s1 = get_st1 st in
  let x = (V2.(index st 2 +%^ index st 3)) in
  let y = (V1.(index s1 2 +%^ index s1 3)) in
  lemma_eq_intro (get_fst x) y;
  let st' = upd st 2 x in
  let s1' = upd s1 2 y in
  lemma_upd_2 st x;
  lemma_upd_2 s1 y;
  lemma_eq_intro (get_st1 st') (s1');
  let x = V2.((index st' 1 ^^ index st' 2) <<< s) in
  let y = V1.((index s1' 1 ^^ index s1' 2) <<< s) in
  lemma_eq_intro (get_fst x) y;
  let st'' = upd st' 1 x in
  let s1'' = upd s1' 1 y in
  lemma_upd_1 st' x;
  lemma_upd_1 s1' y;
  lemma_eq_intro (get_st1 st'') (s1'')


val lemma_line_03_2: st:V2.state -> s:UInt32.t{UInt32.v s < 32} -> Lemma
   (get_st2 (V2.line 0 1 3 s st) == V1.line 0 1 3 s (get_st2 st))
let lemma_line_03_2 st s =
  let s1 = get_st2 st in
  let x = (V2.(index st 0 +%^ index st 1)) in
  let y = (V1.(index s1 0 +%^ index s1 1)) in
  lemma_eq_intro (get_snd x) y;
  let st' = upd st 0 x in
  let s1' = upd s1 0 y in
  lemma_upd_0 st x;
  lemma_upd_0 s1 y;
  lemma_eq_intro (get_st2 st') (s1');
  let x = V2.((index st' 3 ^^ index st' 0) <<< s) in
  let y = V1.((index s1' 3 ^^ index s1' 0) <<< s) in
  lemma_eq_intro (get_snd x) y;
  let st'' = upd st' 3 x in
  let s1'' = upd s1' 3 y in
  lemma_upd_3 st' x;
  lemma_upd_3 s1' y;
  lemma_eq_intro (get_st2 st'') (s1'')

val lemma_line_21_2: st:V2.state -> s:UInt32.t{UInt32.v s < 32} -> Lemma
   (get_st2 (V2.line 2 3 1 s st) == V1.line 2 3 1 s (get_st2 st))
let lemma_line_21_2 st s =
  let s1 = get_st2 st in
  let x = (V2.(index st 2 +%^ index st 3)) in
  let y = (V1.(index s1 2 +%^ index s1 3)) in
  lemma_eq_intro (get_snd x) y;
  let st' = upd st 2 x in
  let s1' = upd s1 2 y in
  lemma_upd_2 st x;
  lemma_upd_2 s1 y;
  lemma_eq_intro (get_st2 st') (s1');
  let x = V2.((index st' 1 ^^ index st' 2) <<< s) in
  let y = V1.((index s1' 1 ^^ index s1' 2) <<< s) in
  lemma_eq_intro (get_snd x) y;
  let st'' = upd st' 1 x in
  let s1'' = upd s1' 1 y in
  lemma_upd_1 st' x;
  lemma_upd_1 s1' y;
  lemma_eq_intro (get_st2 st'') (s1'')

val lemma_line_03: st:V2.state -> s:UInt32.t{UInt32.v s < 32} -> Lemma
   (get_st1 (V2.line 0 1 3 s st) == V1.line 0 1 3 s (get_st1 st)
    /\ get_st2 (V2.line 0 1 3 s st) == V1.line 0 1 3 s (get_st2 st))
let lemma_line_03 st s =
  lemma_line_03_1 st s;
  lemma_line_03_2 st s

val lemma_line_21: st:V2.state -> s:UInt32.t{UInt32.v s < 32} -> Lemma
   (get_st1 (V2.line 2 3 1 s st) == V1.line 2 3 1 s (get_st1 st)
   /\ get_st2 (V2.line 2 3 1 s st) == V1.line 2 3 1 s (get_st2 st))
let lemma_line_21 st s =
  lemma_line_21_1 st s;
  lemma_line_21_2 st s

val lemma_round: st:V2.state -> Lemma
  (get_st1 (V2.round st) == V1.round (get_st1 st) /\ get_st2 (V2.round st) == V1.round (get_st2 st))
let lemma_round st =
  lemma_line_03 st 16ul;
  let st = V2.line 0 1 3 16ul st in
  lemma_line_21 st 12ul;
  let st = V2.line 2 3 1 12ul st in
  lemma_line_03 st 8ul;
  let st = V2.line 0 1 3 8ul st in
  lemma_line_21 st 7ul 


val lemma_diagonal_round: st:V2.state -> Lemma
  (get_st1 (V2.diagonal_round st) == V1.diagonal_round (get_st1 st)
   /\ get_st2 (V2.diagonal_round st) == V1.diagonal_round (get_st2 st))
let lemma_diagonal_round st =
  lemma_shuffle_row0123 st;
  let st = V2.shuffle_rows_0123 st in
  lemma_round st;
  let st = V2.round st in
  lemma_shuffle_row0321 st


val lemma_double_round: st:V2.state -> Lemma
  (get_st1 (V2.double_round st) == V1.double_round (get_st1 st)
   /\ get_st2 (V2.double_round st) == V1.double_round (get_st2 st))
let lemma_double_round st =
  lemma_round st;
  let st = V2.round st in
  lemma_diagonal_round st
