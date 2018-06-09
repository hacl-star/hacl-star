module Lib.ByteSequence

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes

let to_lbytes (s:bytes) = s
let to_bytes #len (s:lbytes len) = s

val nat_from_intseq_be_:#t:m_inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)})  (decreases (len))
let rec nat_from_intseq_be_ #t #len b =
  if len = 0 then 0
  else
    let l = uint_to_nat #t (last #(uint_t t) #len b) in
    let pre : intseq t (decr len) = prefix #(uint_t t) #len b (decr len) in
    let shift = pow2 (bits t) in
    let n' : n:nat{n < pow2 ((len-1) * bits t)}  = nat_from_intseq_be_ #t #(decr len) pre in
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
  match len,b with
  | 0, _ -> (0)
  | _, h::tt ->
    let shift = pow2 (bits t) in
    let n' : n:nat{n < pow2 ((len-1) * bits t)}  = nat_from_intseq_le_ #t #(decr len) tt in
    let l = uint_to_nat #t h in
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
  if len = 0 then []
  else (
    let len' = decr len in
    let byte = u8 (n % 256) in
    let n' =  n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len');
    assert( n' < pow2 (8 * len' ));
    let b' : intseq U8 len' = nat_to_bytes_be_ len' n' in
    let b  : intseq U8 len = snoc #uint8 #len' b' byte in
    assert(b' == prefix b len');
    assert(byte == last #uint8 #len b);
    b)
let nat_to_bytes_be = nat_to_bytes_be_

val nat_to_bytes_le_:
  len:size_nat -> n:nat{n < pow2 (8 * len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_le #U8 #len b}) (decreases (len))
let rec nat_to_bytes_le_ len n =
  if len = 0 then  []
  else
    let len = decr len in
    let byte = u8 (n % 256) in
    let n' = n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len);
    assert(n' < pow2 (8 * len ));
    let b' : intseq U8 len = nat_to_bytes_le_ len n' in
    let b = byte :: b' in
    b

let nat_to_bytes_le = nat_to_bytes_le_

let uint_to_bytes_le #t n =
  nat_to_bytes_le (numbytes t) (uint_to_nat n)

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

