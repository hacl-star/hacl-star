module Lib.ByteSequence

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes
open Lib.LoopCombinators

friend Lib.Sequence

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1"

private
let decr (x:size_nat{x > 0}) : size_nat = x - 1

val nat_from_intseq_be_: #t:inttype -> b:seq (uint_t t) -> Tot (n:nat{n < pow2 (length b * bits t)}) (decreases (length b))
let rec nat_from_intseq_be_ #t b =
  let len = length b in
  if len = 0 then 0
  else
    let l = uint_to_nat #t (seq_index b (len - 1)) in
    let pre = seq_sub b 0 (len - 1) in //prefix #(uint_t t) #len b (decr len)
    let shift = pow2 (bits t) in
    let n': n:nat{n < pow2 ((len-1) * bits t)} = nat_from_intseq_be_ #t pre in
    assert (l <= shift - 1);
    assert (l + shift * n' <= shift * (n' + 1) - 1);
    assert (n' + 1 <= pow2 ((len -1) * bits t));
    assert (shift * (n' + 1) <= shift * pow2 (len * bits t - bits t));
    assert (shift * (n' + 1) <= pow2 (bits t) * pow2 (len * bits t - bits t));
    Math.Lemmas.pow2_plus (bits t) ( len * bits t - bits t);
    assert (shift * (n' + 1) <= pow2 (len  * bits t));
    l + shift * n'

let nat_from_intseq_be = nat_from_intseq_be_

val nat_from_intseq_le_:#t:inttype -> b:seq (uint_t t) -> Tot (n:nat{n < pow2 (length b * bits t)}) (decreases (length b))
let rec nat_from_intseq_le_ #t b = 
  let len = length b in
  if len = 0 then 0
  else
    let shift = pow2 (bits t) in
    let tt = seq_sub b 1 (len - 1) in
    let n' : n:nat{n < pow2 ((len-1) * bits t)} = nat_from_intseq_le_ #t tt in
    let l = uint_to_nat #t (seq_index b 0) in
    assert (l <= shift - 1);
    assert (l + shift * n' <= shift * (n' + 1) - 1);
    assert (n' + 1 <= pow2 ((len -1) * bits t));
    assert (shift * (n' + 1) <= pow2 (bits t) * pow2 (len * bits t - bits t));
    Math.Lemmas.pow2_plus (bits t) ( len * bits t - bits t);
    assert (shift * (n' + 1) <= pow2 (len  * bits t));
    l + shift * n'

let nat_from_intseq_le = nat_from_intseq_le_
let nat_from_bytes_be = nat_from_intseq_be #U8
let nat_from_bytes_le = nat_from_intseq_le #U8

val nat_to_bytes_be_:
  len:nat -> n:nat{ n < pow2 (8 * len)} ->
  Tot (b:bytes {length b == len /\ n == nat_from_intseq_be #U8 b}) (decreases len)
let rec nat_to_bytes_be_ len n =
  if len = 0 then create #(uint_t U8) len (nat_to_uint 0)
  else (
    let len' = len - 1 in
    let byte = u8 (n % 256) in
    let n' = n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len');
    assert (n' < pow2 (8 * len'));
    let b' = nat_to_bytes_be_ len' n' in
    let b  = seq_concat b' (create 1 byte) in
    //let b  : lbytes len = snoc #uint8 #len' b' byte in
    //Lib.Sequence.Lemmas.concat_subs b' (create 1 byte);
    assume (seq_sub b 0 len' == b');
    assume (seq_sub b len' 1 == create 1 byte);
    assert (seq_index (create 1 byte) 0 == byte);
    assert (b' == seq_sub b 0 len');
    assert (create 1 byte == seq_sub b len' 1);
    assert (seq_index (seq_sub b len' 1) 0 == seq_index b len');
    assert (byte == seq_index b len');
    b)

let nat_to_bytes_be = nat_to_bytes_be_

val nat_to_bytes_le_:
    len:nat
  -> n:nat{n < pow2 (8 * len)}
  -> Tot (b:bytes {length b == len /\ n == nat_from_intseq_le b}) (decreases len)
let rec nat_to_bytes_le_ len n =
  if len = 0 then create #(uint_t U8) len (nat_to_uint 0)
  else
    let len' = len - 1 in
    let byte = u8 (n % 256) in
    let n' = n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len');
    assert(n' < pow2 (8 * len'));
    let b' = nat_to_bytes_le_ len' n' in
    let b = seq_concat (create 1 byte) b' in
    //let b  : lbytes len = snoc #uint8 #len' b' byte in
    //Lib.Sequence.Lemmas.concat_subs b' (create 1 byte);
    assume (seq_sub b 0 1 == create 1 byte);
    assume (seq_sub b 1 len' == b');
    assert (seq_index (create 1 byte) 0 == byte);
    assert (b' == seq_sub b 1 len');
    assert (create 1 byte == seq_sub b 0 1);
    assert (seq_index (seq_sub b 0 1) 0 == seq_index b 0);
    assert (byte == seq_index b 0);
    b

let nat_to_bytes_le = nat_to_bytes_le_

val index_nat_to_bytes_le:
    len:size_nat
  -> n:nat{n < pow2 (8 * len)}
  -> i:nat{i < len}
  -> Lemma (seq_index (nat_to_bytes_le len n) i == u8 (n / pow2 (8 * i) % pow2 8))
let rec index_nat_to_bytes_le len n i =
  if i = 0 then ()
  else
    begin
    index_nat_to_bytes_le (len - 1) (n / 256) (i - 1);
    assert (seq_index (nat_to_bytes_le (len - 1) (n / 256)) (i - 1) ==
            u8 ((n / 256) / pow2 (8 * (i - 1)) % pow2 8));
    assert_norm (pow2 8 == 256);
    Math.Lemmas.division_multiplication_lemma n (pow2 8) (pow2 (8 * (i - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (i - 1));
    assert (n / pow2 8 / pow2 (8 * (i - 1)) == n / (pow2 8 * pow2 (8 * i - 8)))
    end

let uint_to_bytes_le #t n =
  nat_to_bytes_le (numbytes t) (uint_to_nat n)

let index_uint_to_bytes_le #t u =
  Classical.forall_intro (index_nat_to_bytes_le (numbytes t) (uint_to_nat u))

let uint_to_bytes_be #t n =
  nat_to_bytes_be (numbytes t) (uint_to_nat n)

let uint_from_bytes_le #t b =
  let n = nat_from_intseq_le #U8 b in
  nat_to_uint #t n

let uint_from_bytes_be #t b =
  let n = nat_from_intseq_be #U8 b in
  nat_to_uint #t n

let uints_to_bytes_le #t #len l =
  let b = create (len * numbytes t) (u8 0) in
  repeati len (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_le  l.[i])) b

let uints_to_bytes_be #t #len l =
  let b = create (len * numbytes t) (u8 0) in
  repeati len (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_be l.[i])) b

let uints_from_bytes_le #t #len b =
  let l = create #(uint_t t) len (nat_to_uint 0) in
  repeati len (fun i l -> l.[i] <- uint_from_bytes_le (sub b (i * numbytes t) (numbytes t))) l

let uints_from_bytes_be #t #len b =
  let l = create #(uint_t t) len (nat_to_uint 0) in
  repeati len (fun i l -> l.[i] <- uint_from_bytes_be (sub b (i * numbytes t) (numbytes t))) l
