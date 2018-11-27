module Lib.ByteSequence

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes
open Lib.LoopCombinators

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1"

val lbytes_eq_inner:
    #len:size_nat
  -> a:lseq uint8 len
  -> b:lseq uint8 len
  -> i:size_nat{i < len}
  -> r:bool
  -> bool
let lbytes_eq_inner #len a b i r =
  let open Lib.RawIntTypes in
  let open FStar.UInt8 in
  r && (u8_to_UInt8 (index a i) =^ u8_to_UInt8 (index b i))

val lbytes_eq_state: len:size_nat -> i:size_nat{i <= len} -> Type0
let lbytes_eq_state len i = bool

let lbytes_eq #len a b =
  repeat_gen len (lbytes_eq_state len) (lbytes_eq_inner a b) true


val nat_from_intseq_be_:
    #t:inttype -> #l:secrecy_level
  -> b:seq (uint_t t l)
  -> Tot (n:nat{n < pow2 (length b * bits t)}) (decreases (length b))
let rec nat_from_intseq_be_ #t #l b =
  let len = length b in
  if len = 0 then 0
  else
    let l = uint_to_nat (Seq.index b (len - 1)) in
    let pre = Seq.slice b 0 (len - 1) in
    let shift = pow2 (bits t) in
    let n' = nat_from_intseq_be_ pre in
    Math.Lemmas.pow2_plus (bits t) (len * bits t - bits t);
    l + shift * n'

let nat_from_intseq_be = nat_from_intseq_be_

val nat_from_intseq_le_:
    #t:inttype -> #l:secrecy_level
  -> b:seq (uint_t t l)
  -> Tot (n:nat{n < pow2 (length b * bits t)}) (decreases (length b))

let rec nat_from_intseq_le_ #t #l b =
  let len = length b in
  if len = 0 then 0
  else
    let shift = pow2 (bits t) in
    let tt = Seq.slice b 1 len in
    let n' = nat_from_intseq_le_ #t #l tt in
    let l = uint_to_nat #t #l (Seq.index b 0) in
    Math.Lemmas.pow2_plus (bits t) ( len * bits t - bits t);
    let n = l + shift * n' in
    n

let nat_from_intseq_le = nat_from_intseq_le_
let nat_from_bytes_be = nat_from_intseq_be #U8
let nat_from_bytes_le = nat_from_intseq_le #U8

val nat_to_bytes_be_:
    len:nat
  -> n:nat{ n < pow2 (8 * len)}
  -> Tot (b:bytes {length b == len /\ n == nat_from_intseq_be #U8 b}) (decreases len)
let rec nat_to_bytes_be_ len n =
  if len = 0 then create len (u8 0)
  else
    let len' = len - 1 in
    let byte = u8 (n % 256) in
    let n' = n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len');
    let b' = nat_to_bytes_be_ len' n' in
    let b  = Seq.append b' (create 1 byte) in
    Seq.append_slices b' (create 1 byte);
    b

let nat_to_bytes_be = nat_to_bytes_be_

val nat_to_bytes_le_:
    len:nat
  -> n:nat{n < pow2 (8 * len)}
  -> Tot (b:bytes {length b == len /\ n == nat_from_intseq_le b}) (decreases len)
let rec nat_to_bytes_le_ len n =
  if len = 0 then create len (u8 0)
  else
    let len' = len - 1 in
    let byte = u8 (n % 256) in
    let n' = n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len');
    let b' = nat_to_bytes_le_ len' n' in
    let b = Seq.append (create 1 byte) b' in
    Seq.append_slices (create 1 byte) b';
    b

let nat_to_bytes_le = nat_to_bytes_le_

val index_nat_to_bytes_le:
    len:size_nat
  -> n:nat{n < pow2 (8 * len)}
  -> i:nat{i < len}
  -> Lemma (Seq.index (nat_to_bytes_le len n) i == u8 (n / pow2 (8 * i) % pow2 8))
let rec index_nat_to_bytes_le len n i =
  if i = 0 then ()
  else
    begin
    index_nat_to_bytes_le (len - 1) (n / 256) (i - 1);
    assert (Seq.index (nat_to_bytes_le (len - 1) (n / 256)) (i - 1) ==
            u8 ((n / 256) / pow2 (8 * (i - 1)) % pow2 8));
    assert_norm (pow2 8 == 256);
    Math.Lemmas.division_multiplication_lemma n (pow2 8) (pow2 (8 * (i - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (i - 1));
    assert (n / pow2 8 / pow2 (8 * (i - 1)) == n / (pow2 8 * pow2 (8 * i - 8)))
    end

let uint_to_bytes_le #t #l n =
  nat_to_bytes_le (numbytes t) (uint_to_nat n)

let index_uint_to_bytes_le #t #l u =
  Classical.forall_intro (index_nat_to_bytes_le (numbytes t) (uint_to_nat u))

let uint_to_bytes_be #t #l n =
  nat_to_bytes_be (numbytes t) (uint_to_nat n)

let uint_from_bytes_le #t #l b =
  let n = nat_from_intseq_le #U8 b in
  nat_to_uint #t #l n

let uint_from_bytes_be #t #l b =
  let n = nat_from_intseq_be #U8 b in
  nat_to_uint #t #l n

let uints_to_bytes_le #t #l #len ul =
  let b = create #uint8 (len * numbytes t) (u8 0) in
  repeati len
    (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_le ul.[i])) b

let uints_to_bytes_be #t #l #len ul =
  let b = create (len * numbytes t) (u8 0) in
  repeati len
    (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_be ul.[i])) b

let uints_from_bytes_le #t #l #len b =
  let l = create #(uint_t t l) len (nat_to_uint 0) in
  repeati len
    (fun i l -> l.[i] <- uint_from_bytes_le (sub b (i * numbytes t) (numbytes t))) l

let uints_from_bytes_be #t #l #len b =
  let l = create #(uint_t t l) len (nat_to_uint 0) in
  repeati len
    (fun i l -> l.[i] <- uint_from_bytes_be (sub b (i * numbytes t) (numbytes t))) l
