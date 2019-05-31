module Hacl.Impl.Bignum.Convert

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Bignum.Core

module Seq = Lib.Sequence
module B = FStar.Bytes
module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val bytes_to_bignum_:
     #len:bn_len
  -> #resLen:bn_len{v len = 8 * v resLen}
  -> input:lbuffer8 len
  -> res:lbignum resLen
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
let bytes_to_bignum_ #len #resLen input res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc res) h0 h1 in
  Lib.Loops.for 0ul resLen inv
  (fun i ->
    res.(resLen -. i -. 1ul) <- uint_from_bytes_be (sub input (8ul *. i) 8ul)
  )

val bytes_to_bignum:
     #len:bn_len
  -> input:lbuffer8 len
  -> res:lbignum (blocks len 8ul){8 * v (blocks len 8ul) < max_size_t}
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bytes_to_bignum #len input res =
  push_frame ();
  let num_words = blocks len 8ul in
  let tmpLen = 8ul *. num_words in
  let m = len %. 8ul in
  let ind = if m =. 0ul then 0ul else 8ul -. m in

  let tmp = create tmpLen (u8 0) in
  let tmpLen1 = tmpLen -. ind in
  let tmp1 = sub tmp ind tmpLen1 in
  copy tmp1 input;
  bytes_to_bignum_ tmp res;
  pop_frame ()

inline_for_extraction noextract
val bignum_to_bytes_:
     #len:bn_len
  -> #resLen:bn_len{v resLen = 8 * v len}
  -> input:lbignum len
  -> res:lbuffer8 resLen
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
let bignum_to_bytes_ #len #resLen input res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc res) h0 h1 in
  Lib.Loops.for 0ul len inv
  (fun i ->
    let tmp = input.(len -. i -. 1ul) in
    uint_to_bytes_be (sub res (8ul *. i) 8ul) tmp
  )

val bignum_to_bytes:
     #len:bn_len{v len > 0}
  -> input:lbignum (blocks len 8ul){8 * v (blocks len 8ul) < max_size_t}
  -> res:lbuffer8 len
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bignum_to_bytes #len input res = admit();
  push_frame ();
  let num_words = blocks len 8ul in
  let tmpLen = 8ul *. num_words in
  let m = len %. 8ul in
  let ind = if m =. 0ul then 0ul else 8ul -. m in

  let tmp = create tmpLen (u8 0) in
  bignum_to_bytes_ input tmp;
  let tmpLen1 = tmpLen -. ind in
  let tmp1 = sub tmp ind tmpLen1 in
  copy res tmp1;
  pop_frame ()

// Prints uints64 chunks in little-endian, though inner uint64 chunks
// in big-endian.
val bignum_to_bytes_direct:
     #len:bn_len{8 * v len < max_size_t}
  -> input:lbignum len
  -> res:lbuffer8 (8ul *. len)
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bignum_to_bytes_direct #len input res =
  push_frame ();

  let h0 = ST.get () in
  let inv h1 i = modifies (loc res) h0 h1 in
  Lib.Loops.for 0ul len inv
  (fun i ->
    let tmp = input.(i) in
    uint_to_bytes_be (sub res (8ul *. i) 8ul) tmp
  );

  pop_frame ()

#reset-options

/// Converts nat to b64 base, lsb first (little endian)
inline_for_extraction noextract
val nat_to_list64: y:nat -> Tot (l:list pub_uint64{List.Tot.length l > 0}) (decreases y)
let rec nat_to_list64 y =
    if y <= maxint U64
    then [uint y]
    else uint (y % (modulus U64)) :: nat_to_list64 (y / (modulus U64))

/// Same as nat_to_list64, but converts to the secure 64 ints.
inline_for_extraction noextract
val nat_to_list64_sec:
       x:nat
    -> l:list uint64{ List.Tot.length l == List.Tot.length (nat_to_list64 x) }
let nat_to_list64_sec x = normalize_term (List.Tot.map secret (nat_to_list64 x))

/// List64 to nat conversion.
inline_for_extraction noextract
val list64_sec_to_nat: l:list uint64{ List.Tot.length l > 0 } -> Tot nat
let rec list64_sec_to_nat l = match l with
  | [x] -> v x
  | x::tl -> v x + list64_sec_to_nat tl * modulus U64

/// Relatively "small" nats, which fit into 512 Mb.
/// Bignums of the related length satisfy bn_len_strict.
let issnat (n:nat) =
    List.Tot.length (nat_to_list64_sec n) * 64 <= max_size_t /\
    normalize (List.Tot.length (nat_to_list64_sec n) * 64 <= max_size_t)

type snat = n:nat{issnat n}

inline_for_extraction noextract
val nat_bytes_num: x:snat -> r:size_t { v r = List.Tot.length (nat_to_list64_sec x) }
let nat_bytes_num x = normalize_term (size (List.Tot.length (nat_to_list64_sec x)))

noextract
let example_snat:snat = assert_norm(issnat 12345678901234567890); 12345678901234567890

/// Nat representation of bigint.
noextract
val as_snat:
     #eLen:bn_len
  -> h:mem
  -> lbignum eLen
  -> GTot nat
let as_snat #eLen h e =
  let s = as_seq h e in
  let l = Seq.Properties.seq_to_list s in
  list64_sec_to_nat l

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

/// Converts nat to the bignum, for that creates a bignum of exact length required.
inline_for_extraction noextract
val nat_to_bignum_exact:
     input:snat
  -> StackInline (lbignum (nat_bytes_num input))
    (requires fun _ -> true)
    (ensures  fun h0 b h1 ->
     live h1 b /\
     stack_allocated b h0 h1 (Seq.of_list (nat_to_list64_sec input)))
let nat_to_bignum_exact input = createL (nat_to_list64_sec input)

/// Converts nat to the bignum, but allows to allocate bigger buffer for the bignum returned.
inline_for_extraction noextract
val nat_to_bignum:
     #k:bn_len
  -> input:snat { v (nat_bytes_num input) <= v k }
  -> StackInline (lbignum k)
    (requires fun _ -> true)
    (ensures  fun h0 b h1 ->
     live h1 b /\
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

  admit();

  res
