module Lib.ByteBuffer

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module Raw = Lib.RawIntTypes

friend Lib.ByteSequence
friend Lib.IntTypes
friend FStar.Endianness

module E = LowStar.Endianness

(*
 * Despite befriending IntTypes this module enforces secrecy. The only exception,
 * for backwards compatibility, is `lbytes_eq`, which declassifies its result.
 *
 * We befriend IntTypes (or use RawIntTypes) to call into LowStar.Endianness library
 * for endianness conversions, which uses public machine integers.
 * E.g. `uint_to_bytes_le` loads a secret integer into a buffer of secret bytes by
 * internally casting the integer to a public machine integer, calling into LowStar,
 * and converting the result back to secret bytes.
 *
 * We use RawIntTypes when possible and only when this would be inconvenient
 * rely on opening the definitions in IntTypes. Specifically, only
 * `uint_from_bytes_le`, uint_from_bytes_be`, `uint_to_bytes_le`, and `uint_to_bytes_be`
 * rely on definitions in IntTypes. Alternatively, RawIntTypes could be used to cast
 * sequences and buffers of secret integers to sequences and buffers of machine integers,
 * but this would be too cumbersome.
*)

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

let uint_to_be #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, PUB -> LowStar.Endianness.htobe16 u
  | U16, SEC -> Raw.u16_from_UInt16 (LowStar.Endianness.htobe16 (Raw.u16_to_UInt16 u))
  | U32, PUB -> LowStar.Endianness.htobe32 u
  | U32, SEC -> Raw.u32_from_UInt32 (LowStar.Endianness.htobe32 (Raw.u32_to_UInt32 u))
  | U64, PUB -> LowStar.Endianness.htobe64 u
  | U64, SEC -> Raw.u64_from_UInt64 (LowStar.Endianness.htobe64 (Raw.u64_to_UInt64 u))

let uint_to_le #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, PUB -> LowStar.Endianness.htole16 u
  | U16, SEC -> Raw.u16_from_UInt16 (LowStar.Endianness.htole16 (Raw.u16_to_UInt16 u))
  | U32, PUB -> LowStar.Endianness.htole32 u
  | U32, SEC -> Raw.u32_from_UInt32 (LowStar.Endianness.htole32 (Raw.u32_to_UInt32 u))
  | U64, PUB -> LowStar.Endianness.htole64 u
  | U64, SEC -> Raw.u64_from_UInt64 (LowStar.Endianness.htole64 (Raw.u64_to_UInt64 u))

let uint_from_be #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, PUB -> LowStar.Endianness.be16toh u
  | U16, SEC -> Raw.u16_from_UInt16 (LowStar.Endianness.be16toh (Raw.u16_to_UInt16 u))
  | U32, PUB -> LowStar.Endianness.be32toh u
  | U32, SEC -> Raw.u32_from_UInt32 (LowStar.Endianness.be32toh (Raw.u32_to_UInt32 u))
  | U64, PUB -> LowStar.Endianness.be64toh u
  | U64, SEC -> Raw.u64_from_UInt64 (LowStar.Endianness.be64toh (Raw.u64_to_UInt64 u))

let uint_from_le #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, PUB -> LowStar.Endianness.le16toh u
  | U16, SEC -> Raw.u16_from_UInt16 (LowStar.Endianness.le16toh (Raw.u16_to_UInt16 u))
  | U32, PUB -> LowStar.Endianness.le32toh u
  | U32, SEC -> Raw.u32_from_UInt32 (LowStar.Endianness.le32toh (Raw.u32_to_UInt32 u))
  | U64, PUB -> LowStar.Endianness.le64toh u
  | U64, SEC -> Raw.u64_from_UInt64 (LowStar.Endianness.le64toh (Raw.u64_to_UInt64 u))

let buf_eq_mask #t #len1 #len2 b1 b2 len res =
  let h0 = ST.get() in
  let inv h (i:nat{i <= v len}) =
    modifies1 res h0 h /\
    v (bget h res 0) == v (BS.seq_eq_mask (as_seq h0 b1) (as_seq h0 b2) i)
  in
  Lib.Loops.for 0ul len inv
    (fun i ->
      let z0 = res.(0ul) in
      res.(0ul) <- eq_mask b1.(i) b2.(i) &. res.(0ul);
      let z = res.(0ul) in
      assert (z == BS.seq_eq_mask_inner (as_seq h0 b1) (as_seq h0 b2) (v len) (v i) z0));
  res.(0ul)

let lbytes_eq #len b1 b2 =
  push_frame();
  let res = create 1ul (u8 255) in
  let z = buf_eq_mask b1 b2 len res in
  pop_frame();
  Raw.u8_to_UInt8 z = 255uy

#set-options "--max_fuel 1 --max_ifuel 1"

/// BEGIN using friend Lib.IntTypes

val nat_from_bytes_le_to_n: l:secrecy_level -> b:Seq.seq UInt8.t ->
  Lemma (ensures (BS.nat_from_bytes_le #l b == FStar.Endianness.le_to_n b))
  (decreases (Seq.length b))
let rec nat_from_bytes_le_to_n l b =
  if Seq.length b = 0 then ()
  else nat_from_bytes_le_to_n l (Seq.tail b)

val nat_from_bytes_be_to_n: l:secrecy_level -> b:Seq.seq UInt8.t ->
  Lemma (ensures (BS.nat_from_bytes_be #l b == FStar.Endianness.be_to_n b))
  (decreases (Seq.length b))
let rec nat_from_bytes_be_to_n l b =
  if Seq.length b = 0 then ()
  else nat_from_bytes_be_to_n l (Seq.slice b 0 (Seq.length b - 1))

let uint_from_bytes_le #t #l i =
  let h0 = ST.get () in  
  nat_from_bytes_le_to_n l (as_seq h0 i);
  match t with
  | U8 -> i.(0ul)
  | U16 -> let u = E.load16_le i in cast #t #l U16 l u
  | U32 -> let u = E.load32_le i in cast #t #l U32 l u
  | U64 -> let u = E.load64_le i in cast #t #l U64 l u
  | U128 ->
    let u = E.load128_le i in
    cast #t #l U128 l u

let uint_from_bytes_be #t #l i =
  let h0 = ST.get () in
  nat_from_bytes_be_to_n l (as_seq h0 i);
  match t with
  | U8 -> i.(0ul)
  | U16 -> let u = E.load16_be i in cast #t #l U16 l u
  | U32 -> let u = E.load32_be i in cast #t #l U32 l u
  | U64 -> let u = E.load64_be i in cast #t #l U64 l u
  | U128 ->
    let u = E.load128_be i in
    cast #t #l U128 l u

val nat_to_bytes_n_to_le: len:size_nat -> l:secrecy_level -> n:nat{n < pow2 (8 * len)} ->
  Lemma (ensures Seq.equal (FStar.Endianness.n_to_le len n) 
                           (BS.nat_to_bytes_le #l len n))
  (decreases len)
let rec nat_to_bytes_n_to_le len l n =
  if len = 0 then () else
    begin
    Math.Lemmas.division_multiplication_lemma n (pow2 8) (pow2 (8 * (len - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (len - 1));
    nat_to_bytes_n_to_le (len - 1) l (n / 256)
    end

val nat_to_bytes_n_to_be: len:size_nat -> l:secrecy_level -> n:nat{n < pow2 (8 * len)} ->
  Lemma (ensures (Seq.equal (FStar.Endianness.n_to_be len n)
                            (BS.nat_to_bytes_be #l len n)))
  (decreases len)
let rec nat_to_bytes_n_to_be len l n =
  if len = 0 then () else
    begin
    Math.Lemmas.division_multiplication_lemma n (pow2 8) (pow2 (8 * (len - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (len - 1));
    nat_to_bytes_n_to_be (len - 1) l (n / 256)
    end

let uint_to_bytes_le #t #l o i =
  match t with
  | U1 | U8 ->
    o.(0ul) <- i;
    let h1 = ST.get () in
    assert (Seq.equal (as_seq h1 o) (BS.nat_to_intseq_le_ #U8 #l (numbytes t) (Raw.uint_to_nat i)))
  | U16 ->
    E.store16_le o (Raw.u16_to_UInt16 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_le (numbytes t) l (v i)
  | U32 ->
    E.store32_le o (Raw.u32_to_UInt32 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_le (numbytes t) l (v i)
  | U64 ->
    E.store64_le o (Raw.u64_to_UInt64 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_le (numbytes t) l (v i)
  | U128 ->
    E.store128_le o (Raw.u128_to_UInt128 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_le (numbytes t) l (v i)

let uint_to_bytes_be #t #l o i =
  match t with
  | U1 | U8 ->
    o.(0ul) <- i;
    let h1 = ST.get () in
    assert (Seq.equal (as_seq h1 o) (BS.nat_to_intseq_be_ #U8 #l (numbytes t) (Raw.uint_to_nat i)))
  | U16 ->
    E.store16_be o (Raw.u16_to_UInt16 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_be (numbytes t) l (v i)
  | U32 ->
    E.store32_be o (Raw.u32_to_UInt32 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_be (numbytes t) l (v i)
  | U64 ->
    E.store64_be o (Raw.u64_to_UInt64 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_be (numbytes t) l (v i)
  | U128 ->
    E.store128_be o (Raw.u128_to_UInt128 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_be (numbytes t) l (v i)

/// END using friend Lib.IntTypes

module Seq = Lib.Sequence

let uints_from_bytes_le #t #l #len o i =
  let h0 = ST.get() in
  [@ inline_let]
  let spec (h:mem) : GTot (j:size_nat{j < v len} -> uint_t t l) =
    let i0 = as_seq h i in
    fun j -> BS.uint_from_bytes_le (Seq.sub i0 (j * numbytes t) (numbytes t))
  in
  fill h0 len o spec (fun j ->
    let h = ST.get() in
    let bj = sub i (j *! (size (numbytes t))) (size (numbytes t)) in
    let r = uint_from_bytes_le bj in
    as_seq_gsub h i (j *! size (numbytes t)) (size (numbytes t));
    r);
  let h1 = ST.get() in
  assert (Seq.equal (as_seq h1 o) (BS.uints_from_bytes_le (as_seq h0 i)))

let uints_from_bytes_be #t #l #len o i =
  let h0 = ST.get() in
  [@ inline_let]
  let spec (h:mem) : GTot (j:size_nat{j < v len} -> uint_t t l) =
    let i0 = as_seq h i in
    fun j -> BS.uint_from_bytes_be (Seq.sub i0 (j * numbytes t) (numbytes t))
  in
  fill h0 len o spec (fun j ->
    let h = ST.get() in
    let bj = sub i (j *! (size (numbytes t))) (size (numbytes t)) in
    let r = uint_from_bytes_be bj in
    as_seq_gsub h i (j *! size (numbytes t)) (size (numbytes t));
    r);
  let h1 = ST.get() in
  assert (Seq.equal (as_seq h1 o) (BS.uints_from_bytes_be (as_seq h0 i)))

#set-options "--z3rlimit 150"

let uints_to_bytes_le #t #l len o i =
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in
  [@ inline_let]
  let spec (h:mem) = BS.uints_to_bytes_le_inner (as_seq h i) in
  fill_blocks h0 (size (numbytes t)) len o a_spec (fun _ _ -> ()) (fun _ -> loc_none) spec
    (fun j -> uint_to_bytes_le (sub o (mul_mod j (size (numbytes t))) (size (numbytes t))) i.(j));
  assert_norm (BS.uints_to_bytes_le (as_seq h0 i) ==
               norm [delta] BS.uints_to_bytes_le (as_seq h0 i))

let uints_to_bytes_be #t #l len o i =
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in
  [@ inline_let]
  let spec (h:mem) = BS.uints_to_bytes_be_inner (as_seq h i) in
  fill_blocks h0 (size (numbytes t)) len o a_spec (fun _ _ -> ()) (fun _ -> loc_none) spec
    (fun j -> uint_to_bytes_be (sub o (mul_mod j (size (numbytes t))) (size (numbytes t))) i.(j));
  assert_norm (BS.uints_to_bytes_be (as_seq h0 i) ==
               norm [delta] BS.uints_to_bytes_be (as_seq h0 i))

let uint_at_index_le #t #l #len i idx =
  let b = sub i (idx *! (size (numbytes t))) (size (numbytes t)) in
  uint_from_bytes_le b

let uint_at_index_be #t #l #len i idx =
  let b = sub i (idx *! (size (numbytes t))) (size (numbytes t)) in
  uint_from_bytes_be b
