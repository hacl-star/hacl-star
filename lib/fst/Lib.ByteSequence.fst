module Lib.ByteSequence

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"

let to_lbytes (s:bytes) = s

let to_bytes #len (s:lbytes len) = s

private
let decr (x:size_nat{x > 0}) : size_nat = x - 1

val nat_from_intseq_be_:#t:m_inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)})  (decreases (len))
let rec nat_from_intseq_be_ #t #len b =
  if len = 0 then 0
  else
    let l = uint_to_nat #t (index b (len - 1)) in
    let pre : intseq t (decr len) = sub b 0 (decr len) in //prefix #(uint_t t) #len b (decr len)
    let shift = pow2 (bits t) in
    let n': n:nat{n < pow2 ((len-1) * bits t)} = nat_from_intseq_be_ #t #(decr len) pre in
    assert (l <= shift - 1);
    assert (l + shift * n' <= shift * (n' + 1) - 1);
    assert (n' + 1 <= pow2 ((len -1) * bits t));
    assert (shift * (n' + 1) <= shift * pow2 (len * bits t - bits t));
    assert (shift * (n' + 1) <= pow2 (bits t) * pow2 (len * bits t - bits t));
    Math.Lemmas.pow2_plus (bits t) ( len * bits t - bits t);
    assert (shift * (n' + 1) <= pow2 (len  * bits t));
    l + shift * n'

let nat_from_intseq_be = nat_from_intseq_be_

val nat_from_intseq_le_:#t:m_inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)}) (decreases (len))
let rec nat_from_intseq_le_ #t #len (b:intseq t len)  =
  if len = 0 then 0
  else
    let shift = pow2 (bits t) in
    let tt:intseq t (decr len) = sub b 1 (decr len) in
    let n' : n:nat{n < pow2 ((len-1) * bits t)} = nat_from_intseq_le_ #t #(decr len) tt in
    let l = uint_to_nat #t (index b 0) in
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
  len:size_nat -> n:nat{ n < pow2 (8 * len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_be #U8 #len b}) (decreases (len))
let rec nat_to_bytes_be_ len n =
  if len = 0 then create #(uint_t U8) len (nat_to_uint 0)
  else (
    let len' = decr len in
    let byte = u8 (n % 256) in
    let n' = n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len');
    assert (n' < pow2 (8 * len'));
    let b' : intseq U8 len' = nat_to_bytes_be_ len' n' in
    //let b  : intseq U8 len = snoc #uint8 #len' b' byte in
    let b  : intseq U8 len = concat b' (create 1 byte) in
    Lib.Sequence.Lemmas.concat_subs b' (create 1 byte);
    assert (index (create 1 byte) 0 == byte);
    assert (b' == sub b 0 len');
    assert (create 1 byte == sub b (decr len) 1);
    assert (index (sub b (decr len) 1) 0 == index b (decr len));
    assert (byte == index b (decr len));
    b)

let nat_to_bytes_be = nat_to_bytes_be_

val nat_to_bytes_le_:
    len:size_nat
  -> n:nat{n < pow2 (8 * len)}
  -> Tot (b:intseq U8 len {n == nat_from_intseq_le b}) (decreases len)
let rec nat_to_bytes_le_ len n =
  if len = 0 then create #(uint_t U8) len (nat_to_uint 0)
  else
    let len = decr len in
    let byte = u8 (n % 256) in
    let n' = n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len);
    assert(n' < pow2 (8 * len ));
    let b' : intseq U8 len = nat_to_bytes_le_ len n' in
    let b = concat (create 1 byte) b' in
    Lib.Sequence.Lemmas.concat_subs (create 1 byte) b';
    assert (index (create 1 byte) 0 == byte);
    assert (b' == sub b 1 len);
    assert (create 1 byte == sub b 0 1);
    assert (index (sub b 0 1) 0 == index b 0);
    assert (byte == index b 0);
    b

let nat_to_bytes_le = nat_to_bytes_le_

val index_nat_to_bytes_le:
    len:size_nat
  -> n:nat{n < pow2 (8 * len)}
  -> i:nat{i < len}
  -> Lemma (index (nat_to_bytes_le len n) i == u8 (n / pow2 (8 * i) % pow2 8))
let rec index_nat_to_bytes_le len n i =
  if i = 0 then ()
  else
    begin
    index_nat_to_bytes_le (len - 1) (n / 256) (i - 1);
    assert (index (nat_to_bytes_le (len - 1) (n / 256)) (i - 1) ==
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
  let n = nat_from_intseq_le #U8 #(numbytes t) b in
  nat_to_uint #t n

let uint_from_bytes_be #t b =
  let n = nat_from_intseq_be #U8 #(numbytes t) b in
  nat_to_uint #t n

let uints_to_bytes_le #t (#len:size_nat{len * numbytes t < pow2 32}) (l:intseq t len) : lbytes (len * numbytes t) =
  let b = create (len * numbytes t) (u8 0) in
  repeati len (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_le l.[i])) b

let uints_to_bytes_be #t (#len:size_nat{len * numbytes t < pow2 32}) (l:intseq t len) : lbytes (len * numbytes t) =
  let b = create (len * numbytes t) (u8 0) in
  repeati len (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_be l.[i])) b

let uints_from_bytes_le #t (#len:size_nat{len * numbytes t < pow2 32}) (b:lbytes (len * numbytes t)) : intseq t len =
  let l = create #(uint_t t) len (nat_to_uint 0) in
  repeati len (fun i l -> l.[i] <- uint_from_bytes_le (sub b (i * numbytes t) (numbytes t))) l

let uints_from_bytes_be #t (#len:size_nat{len * numbytes t < pow2 32}) (b:lbytes (len * numbytes t)) : intseq t len =
  let l = create #(uint_t t) len (nat_to_uint 0) in
  repeati len (fun i l -> l.[i] <- uint_from_bytes_be (sub b (i * numbytes t) (numbytes t))) l
