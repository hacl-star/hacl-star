module Vale.Def.Words.Seq_s
open FStar.Mul

#reset-options "--max_fuel 3 --initial_fuel 3"
let two_to_seq_LE #a x =
  let l = [x.lo; x.hi] in
  let s = seq_of_list l in
  lemma_seq_of_list_index l 0;
  lemma_seq_of_list_index l 1;
  seq_of_list l

let two_to_seq_BE #a x =
  let l = [x.hi; x.lo] in
  let s = seq_of_list l in
  lemma_seq_of_list_index l 0;
  lemma_seq_of_list_index l 1;
  seq_of_list l
#reset-options

#reset-options "--max_fuel 5 --initial_fuel 5"
let four_to_seq_LE #a x =
  let l = [x.lo0; x.lo1; x.hi2; x.hi3] in
  let s = seq_of_list l in
  lemma_seq_of_list_index l 0;
  lemma_seq_of_list_index l 1;
  lemma_seq_of_list_index l 2;
  lemma_seq_of_list_index l 3;
  seq_of_list l

let four_to_seq_BE #a x =
  let l = [x.hi3; x.hi2; x.lo1; x.lo0] in
  let s = seq_of_list l in
  lemma_seq_of_list_index l 0;
  lemma_seq_of_list_index l 1;
  lemma_seq_of_list_index l 2;
  lemma_seq_of_list_index l 3;
  seq_of_list l
#reset-options
