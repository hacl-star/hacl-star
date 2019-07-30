module Hacl.Spec.Bignum

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.PrintBuffer

open Hacl.Impl.Bignum.Core

module Seq = Lib.Sequence
module FSeq = FStar.Seq
module B = FStar.Bytes
module L = FStar.List.Tot
module ST = FStar.HyperStack.ST



/// Converts nat to b64 base, lsb first (little endian)
inline_for_extraction noextract
val nat_to_list64: y:nat -> Tot (l:list pub_uint64{L.length l > 0}) (decreases y)
let rec nat_to_list64 y =
    if y <= maxint U64
    then [uint y]
    else uint (y % (modulus U64)) :: nat_to_list64 (y / (modulus U64))

/// Base64 representation preserves order.
val nat_to_list64_order: a:nat -> b:nat -> Lemma
  (requires (a <= b))
  (ensures (L.length (nat_to_list64 a) <=
            L.length (nat_to_list64 b)))
let rec nat_to_list64_order a b =
    if a <= maxint U64 then ()
    else nat_to_list64_order (a / (modulus U64)) (b / (modulus U64))

/// Same as nat_to_list64, but converts to the secure 64 ints.
inline_for_extraction noextract
val nat_to_list64_sec:
       x:nat
    -> l:list uint64{ L.length l == L.length (nat_to_list64 x) }
let nat_to_list64_sec x = normalize_term (L.map secret (nat_to_list64 x))

/// List64 to nat conversion.
inline_for_extraction noextract
val list64_sec_to_nat: l:list uint64{ L.length l > 0 } -> Tot nat
let rec list64_sec_to_nat l = match l with
  | [x] -> v x
  | x::tl -> v x + list64_sec_to_nat tl * modulus U64

/// This conversion is invertible.
val conv_inv1: a:nat -> Lemma
  (list64_sec_to_nat (nat_to_list64_sec a) = a)
let rec conv_inv1 a =
    if a <= maxint U64 then ()
    else conv_inv1 (a / (modulus U64))

val strip_bits: l:list uint64{ L.length l > 0 } -> l':list uint64{ L.length l' > 0 }
let rec strip_bits l = match l with
  | [x] -> [x]
  | (x::xs) -> if eq_u64 x (uint 0) then strip_bits xs else xs

val rev_acc_preserves_length: l:list 'a -> acc:list 'a -> Lemma
  (L.length (L.rev_acc l acc) = L.length l + L.length acc)
let rec rev_acc_preserves_length l acc = match l with
  | [] -> ()
  | hd::tl -> rev_acc_preserves_length tl (hd::acc)

val rev_preserves_length: l:list 'a -> Lemma
  (L.length (L.rev l) = L.length l)
let rec rev_preserves_length l = rev_acc_preserves_length l []

val strip_high_bits: l:list uint64{ L.length l > 0 } -> l':list uint64{ L.length l' > 0 }
let strip_high_bits l =
  rev_preserves_length l;
  rev_preserves_length (strip_bits (L.rev l));
  L.rev (strip_bits (L.rev l))

val msg_after_strip: l:list uint64 { L.length l > 0 } -> Lemma
  (~(eq_u64 (L.last (strip_high_bits l)) (uint 0)) \/ eq_u64 (L.hd l) (uint 0))
let msg_after_strip l = admit()

val conv_inv2: l:list uint64{ L.length l > 0 } -> Lemma
  (let l' = nat_to_list64_sec (list64_sec_to_nat l) in strip_high_bits l == l')
let conv_inv2 l = admit()

/// Relatively "small" nats, which fit into 256 Mb (2147483648 bits).
/// Related bignums' lengths satisfy all the needed library predicates.
noextract
let issnat (n:nat) =
    L.length (nat_to_list64_sec n) * 128 <= max_size_t

type snat = n:nat{issnat n}

/// Nats less than any snat are snats too.
val snat_order: a:nat -> b:nat{a <= b} ->
  Lemma (requires (issnat b)) (ensures (issnat a))
let snat_order a b = nat_to_list64_order a b

inline_for_extraction noextract
val nat_bytes_num: x:snat -> r:size_t { v r = L.length (nat_to_list64_sec x) }
let nat_bytes_num x = normalize_term (size (L.length (nat_to_list64_sec x)))

/// Bignums created of snats are properly sized, their size is bn_len_strict.
val nat_bytes_num_range: x:snat -> Lemma
  (requires true)
  (ensures (v (nat_bytes_num x) * 64 <= max_size_t /\
            v (nat_bytes_num x +. nat_bytes_num x) * 64 <= max_size_t /\
            v (nat_bytes_num x) > 0))
let nat_bytes_num_range _ = ()

/// Type alias for nat to be proper (snat) and fit into the provided bound.
type nat_fits (a:nat) (bound:size_t) = issnat a /\ v (nat_bytes_num a) <= v bound

/// Base64 representation on snats preserves order (specialised version).
val nat_bytes_num_fit: a:nat -> b:snat -> Lemma
  (requires (a <= b))
  (ensures (nat_fits a (nat_bytes_num b)))
let rec nat_bytes_num_fit a b = snat_order a b; nat_to_list64_order a b

/// If element b fits, then any smaller element does too.
val nat_fits_trans: a:nat -> b:nat -> bound:size_t -> Lemma
  (requires (a <= b /\ nat_fits b bound))
  (ensures (nat_fits a bound))
let rec nat_fits_trans a b bound = nat_bytes_num_fit a b

/// Fitting nat is smaller than (2^64)^bound.
val nat_fits_less_pow: a:nat -> bound:size_t -> Lemma
  (requires nat_fits a bound)
  (ensures a < pow2 (64 * v bound))
let nat_fits_less_pow a bound = admit ()

/// Nat representation of bigint.
noextract
val as_snat:
     #eLen:bn_len
  -> h:mem
  -> lbignum eLen
  -> GTot nat
let as_snat #eLen h e =
//  assert (L.length e > 0);
  let x = as_seq h e in
  list64_sec_to_nat (Seq.Properties.seq_to_list x)

/// Number of real words neeeded to represent a number
/// fit into its given bignum representation.
val as_snat_prop:
     #eLen:bn_len_strict
  -> h:mem
  -> e:lbignum eLen
  -> Lemma (nat_fits (as_snat h e) eLen)
let as_snat_prop #eLen h e = admit ()

val as_snat_preserves_stack:
     #eLen:bn_len
  -> e:lbignum eLen
  -> h0:mem
  -> h1:mem
  -> Lemma (requires (as_seq h0 e == as_seq h1 e))
           (ensures (as_snat h0 e = as_snat h1 e))
let as_snat_preserves_stack #eLen e h0 h1 = ()

/// Converts nat to the bignum, for that creates a bignum of exact length required.
inline_for_extraction noextract
val nat_to_bignum_exact:
     input:snat
  -> StackInline (lbignum (nat_bytes_num input))
    (requires fun _ -> true)
    (ensures  fun h0 b h1 ->
     live h1 b /\
     as_snat h1 b = input /\
     stack_allocated b h0 h1 (Seq.of_list (nat_to_list64_sec input)))
let nat_to_bignum_exact input =
  let res = createL (nat_to_list64_sec input) in
  Seq.Properties.lemma_list_seq_bij (nat_to_list64_sec input);
  conv_inv1 input;
  res

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

/// Converts nat to the bignum, but allows to allocate bigger buffer for the bignum returned.
inline_for_extraction noextract
val nat_to_bignum:
     #k:bn_len
  -> input:snat { v (nat_bytes_num input) <= v k }
  -> StackInline (lbignum k)
    (requires fun _ -> true)
    (ensures  fun h0 b h1 ->
     live h1 b /\
     as_snat h1 b = input /\
     stack_allocated b h0 h1
       (Seq.concat (Seq.of_list (nat_to_list64_sec input))
                   (Seq.create (v k - v (nat_bytes_num input)) (uint 0)))
    )
let nat_to_bignum #k input =
  let len: size_t = nat_bytes_num input in
  let created: lbignum len = nat_to_bignum_exact input in
  let res: lbignum k = create k (u64 0) in
  let res_sub: lbignum len = sub res 0ul len in

  copy res_sub created;

  admit(); // must prove that adding extra high bit zeroes doesn't change the number

  res

val bignum_of_uL:
     #len:bn_len
  -> a:lbignum len
  -> h:mem
  -> x:uint64
  -> Lemma (as_snat h a = v x ==> (let s = as_seq h a in Seq.index s 0 == x))
let bignum_of_uL #len a h x = admit()
