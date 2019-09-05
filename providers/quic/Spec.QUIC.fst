module Spec.QUIC

module S = FStar.Seq
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module H = Spec.Hash
module HD = Spec.Hash.Definitions
module C16 = Spec.Cipher16
module AEAD = Spec.AEAD
module HKDF = Spec.HKDF

let prefix: lbytes 11 =
  let l = [0x74uy; 0x6cuy; 0x73uy; 0x31uy; 0x33uy;
           0x20uy; 0x71uy; 0x75uy; 0x69uy; 0x63uy; 0x20uy] in
  let _ = assert_norm (List.Tot.length l == 11) in
  S.seq_of_list l

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 10"
let lemma_hash_lengths (a:ha)
  : Lemma (HD.hash_length a <= 64 /\ HD.word_length a <= 8 /\
    HD.block_length a <= 128 /\ HD.max_input_length a >= pow2 61)
  =
  assert_norm(pow2 61 < pow2 125)
#pop-options

let derive_secret a prk label len =
  let open S in
  let z = S.create 1 0uy in
  let lb = S.create 1 (U8.uint_to_t len) in // len <= 255
  let llen = S.create 1 (U8.uint_to_t (11 + Seq.length label)) in
  let info = z @| lb @| llen @| prefix @| label @| z in
  lemma_hash_lengths a;
  assert_norm(452 < pow2 61);
  HKDF.expand a prk info len

let encode_varint n =
  let open FStar.Endianness in
  if n < pow2 6 then n_to_be 1 n
  else if n < pow2 14 then n_to_be 2 (pow2 14 + n)
  else if n < pow2 30 then n_to_be 4 (pow2 31 + n)
  else n_to_be 8 (pow2 63 + pow2 62 + n)

let suffix (b:bytes) (n:nat{n <= S.length b}) = S.slice b n (S.length b)

let parse_varint_weak (b:bytes{S.length b > 0}) : option (nat62 * vlsize * bytes) =
  let open FStar.Endianness in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  assert_norm(pow2 8 / 0x40 == 4);
  assert_norm(0x4000 < pow2 62 /\ 0x40000000 < pow2 62 /\ 0x4000000000000000 == pow2 62);
  // b0 is the integer interpretation of the first 2 bits of b
  let b0 = U8.v (S.index b 0) / 0x40 in
  if S.length b < pow2 b0 then None else
  let n = be_to_n (S.slice b 0 (pow2 b0)) in
  let suff = S.slice b (pow2 b0) (S.length b) in
  (match b0 with
  | 0 -> Some (n % 0x40, 1, suff)
  | 1 -> Some (n % 0x4000, 2, suff)
  | 2 -> Some (n % 0x40000000, 4, suff)
  | 3 -> Some (n % 0x4000000000000000, 8, suff))


let parse_varint b =
  if S.length b = 0 then None
  else match parse_varint_weak b with
  | None -> None
  | Some(l,vll,suff) ->
    if vlen l <> vll then None else Some(l,suff)

// Move to FStar.Math.Lemmas?
private let lemma_mod_pow2 (a:nat) (b:nat) : Lemma
  (requires a >= b) (ensures pow2 a % pow2 b == 0)
  [SMTPat (pow2 a % pow2 b)]
  =
  let open FStar.Math.Lemmas in
  lemma_div_mod (pow2 a) (pow2 b);
  pow2_minus a b;
  pow2_plus b (a-b)

private let lemma_divrem2 (k:nat) (a:nat) (n:nat)
  : Lemma (requires a >= k /\ n < pow2 k)
  (ensures ((pow2 a + n) % pow2 k == n /\ (pow2 a + n) / pow2 k == pow2 (a - k)))
  =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  modulo_distributivity (pow2 a) n (pow2 k);
  small_mod n (pow2 k);
  lemma_div_mod (pow2 a + n) (pow2 k);
  pow2_minus a k

// We really should have this pattern already...
private let lemma_mod0 (x:pos) : Lemma (0 % x == 0)
  [SMTPat (0 % x)] = ()

// Move to FStar.Math.Lemmas?
private let lemma_pow2_div (a:nat) (b:nat) (k:nat)
  : Lemma (requires a >= k /\ b >= k)
    (ensures (pow2 a + pow2 b) / pow2 k == pow2 (a - k) + pow2 (b - k))
  =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  pow2_plus k (b - k);
  division_addition_lemma (pow2 a) (pow2 k) (pow2 (b-k));
  pow2_minus b k;
  pow2_minus a k

#push-options "--z3rlimit 60"
private let lemma_divrem3 (k:nat) (a:nat) (b:nat) (n:nat)
  : Lemma (requires a >= k /\ b >= k /\ n < pow2 k)
  (ensures (pow2 a + pow2 b + n) % pow2 k == n /\ (pow2 a + pow2 b + n) / pow2 k == pow2 (a - k) + pow2 (b - k))
  =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  modulo_distributivity (pow2 a + pow2 b) n (pow2 k);
  modulo_distributivity (pow2 a) (pow2 b) (pow2 k);
  small_mod n (pow2 k);
  lemma_div_mod (pow2 a + pow2 b + n) (pow2 k);
  lemma_pow2_div a b k
#pop-options


private let lemma_pow2_div2 (a:nat) (b:nat) (c:nat)
  : Lemma ((a / pow2 b) / pow2 c == a / (pow2 (c + b)))
  =
  let open FStar.Math.Lemmas in
  pow2_plus b c;
  division_multiplication_lemma a (pow2 b) (pow2 c)

private let lemma_div_sub_small (l:nat) (n:nat) (x:nat)
  : Lemma (requires l > 1)
  (ensures (n - n % pow2 8) / pow2 (8 `op_Multiply` (l-1)) == n / pow2 (8 `op_Multiply` (l-1)))
  =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  lemma_mod_spec n (pow2 8);
  lemma_pow2_div2 n 8 (8*(l-2));
  lemma_pow2_div2 (n - n % pow2 8) 8 (8*(l-2))

#push-options "--z3rlimit 20"
private let rec lemma_be_index (l:pos) (n:nat{n < pow2 (8 `op_Multiply` l)})
  : Lemma (ensures U8.v (S.index (FStar.Endianness.n_to_be l n) 0)
    == n / pow2 (8 `op_Multiply` (l-1)))
    (decreases %[l])
  =
  let open FStar.Endianness in
  let open FStar.Mul in
  let b = n_to_be l n in
  let b0 = S.index b 0 in
  reveal_be_to_n b;
  if l = 1 then ()
  else
    let b1 = S.last b in
    let b' = S.slice b 0 (l-1) in
    let b0' = S.index b' 0 in
    reveal_be_to_n b';
    assert(U8.v b1 == n % pow2 8);
    lemma_be_to_n_is_bounded b';
    lemma_be_index (l-1) (be_to_n b');
    lemma_pow2_div2 (n - U8.v b1) 8 (8 * (l-1) - 8);
    lemma_div_sub_small l n (U8.v b1)
#pop-options

private let mod_case1 (n:nat) : n:nat{n < pow2 62} =
  let open FStar.Math.Lemmas in
  assert_norm(0x4000 < pow2 62);
  modulo_range_lemma n 0x4000; n % 0x4000

private let lemma_varint_case1 (n:nat{n < pow2 14}) (suff:bytes)
  : Lemma (parse_varint_weak S.(FStar.Endianness.n_to_be 2 (pow2 14 + n) @| suff) ==
    Some (mod_case1 n, 2, suff))
  =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  let b = S.(n_to_be 2 (pow2 14 + n) @| suff) in
  let b0 = U8.v (S.index b 0) / 0x40 in
  lemma_be_index 2 (pow2 14 + n);
  division_multiplication_lemma (pow2 14 + n) 0x100 0x40;
  lemma_divrem2 14 14 n;
  S.append_slices (n_to_be 2 (pow2 14 + n)) suff;
  match b0 with
  | 1 -> assert(parse_varint_weak b == Some (mod_case1 n, 2, suff))

private let mod_case2 (n:nat) : n:nat{n < pow2 62} =
  let open FStar.Math.Lemmas in
  assert_norm(0x40000000 < pow2 62);
  modulo_range_lemma n 0x40000000; n % 0x40000000

private let lemma_varint_case2 (n:nat{n < pow2 30}) (suff:bytes)
  : Lemma (parse_varint_weak S.(FStar.Endianness.n_to_be 4 (pow2 31 + n) @| suff) ==
    Some (mod_case2 n, 4, suff)) =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  let b = S.(n_to_be 4 (pow2 31 + n) @| suff) in
  let b0 = U8.v (S.index b 0) / 0x40 in
  lemma_be_index 4 (pow2 31 + n);
  division_multiplication_lemma (pow2 31 + n) 0x1000000 0x40;
  lemma_divrem2 30 31 n;
  assert(S.length b == 4 + S.length suff /\ b0 == 2 /\ n % 0x40000000 == n);
  S.append_slices (n_to_be 4 (pow2 31 + n)) suff;
  match b0 with
  | 2 -> assert(parse_varint_weak b == Some (n % 0x40000000, 4, suff))

private let mod_case3 (n:nat) : n:nat{n < pow2 62} =
  let open FStar.Math.Lemmas in
  assert_norm(0x4000000000000000 == pow2 62);
  modulo_range_lemma n 0x4000000000000000; n % 0x4000000000000000

let lemma_varint_case3 (n:nat{n < pow2 62}) (suff:bytes)
  : Lemma (parse_varint_weak S.(FStar.Endianness.n_to_be 8 (pow2 63 + pow2 62 + n) @| suff) ==
    Some (mod_case3 n, 8, suff)) =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  assert_norm(pow2 (8 * 0) == 1 /\ pow2 (8 * 1) == 0x100 /\ pow2 (8 * 3) == 0x1000000 /\ pow2 (8 * 7) == 0x100000000000000);
  let b = S.(n_to_be 8 (pow2 63 + pow2 62 + n) @| suff) in
  let b0 = U8.v (S.index b 0) / 0x40 in
  lemma_be_index 8 (pow2 63 + pow2 62 + n);
  division_multiplication_lemma (pow2 63 + pow2 62 + n) 0x100000000000000 0x40;
  lemma_divrem3 62 63 62 n;
  S.append_slices (n_to_be 8 (pow2 63 + pow2 62 + n)) suff;
  match b0 with
  | 3 -> assert(parse_varint_weak b == Some (n % 0x4000000000000000, 8, suff))

#push-options "--z3rlimit 30"
let length_encode (n:nat62) : Lemma
  (let b = encode_varint n in
   let b0 = U8.v (S.index b 0) / 0x40 in
   S.length b == pow2 b0) =
  let b = encode_varint n in
  let b0 = U8.v (S.index b 0) / 0x40 in
  if n < pow2 6 then lemma_be_index 1 n
  else if n < pow2 14 then lemma_be_index 2 (pow2 14+n)
  else if n < pow2 30 then lemma_be_index 4 (pow2 31+n)
  else lemma_be_index 8 (pow2 63+pow2 62+n)
#pop-options




let lemma_varint_weak (n:nat62) (suff:bytes) : Lemma
  (parse_varint_weak S.(encode_varint n @| suff) == Some (n, vlen n, suff)) =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  assert_norm(pow2 8 / 0x40 == 4);
  assert_norm(0x4000 < pow2 62 /\ 0x40000000 < pow2 62 /\ 0x4000000000000000 == pow2 62);
  assert_norm(pow2 6 == 0x40 /\ pow2 14 == 0x4000 /\ pow2 30 == 0x40000000 /\ pow2 62 == 0x4000000000000000);
  assert_norm(pow2 (8 * 0) == 1 /\ pow2 (8 * 1) == 0x100 /\ pow2 (8 * 3) == 0x1000000 /\ pow2 (8 * 7) == 0x100000000000000);
  assert_norm(0x100 * 0x40 == 0x4000 /\ 0x1000000 * 0x40 == 0x40000000);
  let b = S.(encode_varint n @| suff) in
  let b0 = U8.v (S.index b 0) / 0x40 in
  length_encode n;
  if S.length b >= pow2 b0 then
    let n' = be_to_n (S.slice b 0 (pow2 b0)) in
    if n < pow2 6 then
    begin
      lemma_be_index 1 n;
      small_div n (pow2 6); small_mod n (pow2 6);
      S.lemma_empty (suffix b 1);
      S.append_slices (encode_varint n) suff;
      match b0 with
      | 0 -> assert(parse_varint_weak b == Some (n' % 0x40, 1, suff))
    end
    else if n < pow2 14 then lemma_varint_case1 n suff
    else if n < pow2 30 then lemma_varint_case2 n suff
    else lemma_varint_case3 n suff


let lemma_varint n suff =
  lemma_varint_weak n suff


let lemma_be_index_bytes (l:pos) (b:bytes) : Lemma
  (requires S.length b >= l)
  (ensures FStar.Endianness.be_to_n (S.slice b 0 l) / pow2 (8 `op_Multiply` (l-1)) = U8.v (S.index b 0)) =
  let open FStar.Endianness in
  let n = be_to_n (S.slice b 0 l) in
  lemma_be_to_n_is_bounded (S.slice b 0 l);
  lemma_be_index l n;
  n_to_be_be_to_n l (S.slice b 0 l)


let lemma_varint_weak_safe (b1:bytes) (b2:bytes) : Lemma
  (requires
    S.length b1 <> 0 /\
    S.length b2 <> 0 /\
    parse_varint_weak b1 = parse_varint_weak b2)
  (ensures parse_varint b1 = None \/ S.equal b1 b2) =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  let b01 = U8.v (S.index b1 0) / 0x40 in
  let b02 = U8.v (S.index b2 0) / 0x40 in
  if S.length b1 >= pow2 b01 && S.length b2 >= pow2 b02 then
  let n1 = be_to_n (S.slice b1 0 (pow2 b01)) in
  let n2 = be_to_n (S.slice b2 0 (pow2 b02)) in
  let suff1 = S.slice b1 (pow2 b01) (S.length b1) in
  let suff2 = S.slice b2 (pow2 b02) (S.length b2) in
  assert (S.equal suff1 (S.slice b1 (pow2 b01) (S.length b1)));
  assert (S.equal suff2 (S.slice b2 (pow2 b02) (S.length b2)));
  lemma_be_index_bytes (pow2 b01) b1;
  lemma_be_index_bytes (pow2 b02) b2;
  division_multiplication_lemma n1 (pow2 (8 * (pow2 b01-1))) 0x40;
  division_multiplication_lemma n2 (pow2 (8 * (pow2 b02-1))) 0x40;
  n_to_be_be_to_n (pow2 b01) (S.slice b1 0 (pow2 b01));
  n_to_be_be_to_n (pow2 b02) (S.slice b2 0 (pow2 b02));
  match b01,b02 with
  | 0,0 ->
    assert (S.equal (S.slice b1 0 1) (S.slice b2 0 1));
    assert (S.equal (S.slice b1 1 (S.length b1)) (S.slice b2 1 (S.length b2)));
    assert (S.equal b1 S.(S.slice b1 0 1 @| S.slice b1 1 (S.length b1)));
    assert (S.equal b2 S.(S.slice b2 0 1 @| S.slice b2 1 (S.length b2)))
  | 1,1 ->
    assert (n1 % 0x4000 = n2 % 0x4000);
    assert_norm (pow2 (8 * (pow2 1-1)) * 0x40 = 0x4000);
    assert (n1 / 0x4000 = n2 / 0x4000);
    assert (S.equal (S.slice b1 0 2) (S.slice b2 0 2));
    assert (S.equal b1 S.(S.slice b1 0 2 @| S.slice b1 2 (S.length b1)));
    assert (S.equal b2 S.(S.slice b2 0 2 @| S.slice b2 2 (S.length b2)))
  | 2,2 ->
    assert (n1 % 0x40000000 = n2 % 0x40000000);
    assert_norm (pow2 (8 * (pow2 2-1)) * 0x40 = 0x40000000);
    assert (n1 / 0x40000000 = n2 / 0x40000000);
    assert (S.equal (S.slice b1 0 4) (S.slice b2 0 4));
    assert (S.equal b1 S.(S.slice b1 0 4 @| S.slice b1 4 (S.length b1)));
    assert (S.equal b2 S.(S.slice b2 0 4 @| S.slice b2 4 (S.length b2)))
  | 3,3 ->
    assert (n1 % 0x4000000000000000 = n2 % 0x4000000000000000);
    assert_norm (pow2 (8 * (pow2 3-1)) * 0x40 = 0x4000000000000000);
    assert (n1 / 0x4000000000000000 = n2 / 0x4000000000000000);
    assert (S.equal (S.slice b1 0 8) (S.slice b2 0 8));
    assert (S.equal b1 S.(S.slice b1 0 8 @| S.slice b1 8 (S.length b1)));
    assert (S.equal b2 S.(S.slice b2 0 8 @| S.slice b2 8 (S.length b2)))


let lemma_varint_safe (b1:bytes) (b2:bytes) : Lemma
  (requires
    S.length b1 <> 0 /\
    S.length b2 <> 0 /\
    parse_varint b1 = parse_varint b2)
  (ensures parse_varint b1 = None \/ S.equal b1 b2) =
  match parse_varint_weak b1, parse_varint_weak b2 with
  | None, _
  | _, None -> ()
  | Some (l1,vll1,suff1), Some (l2,vll2,suff2) ->
    if vll1 = vlen l1 && vll2 = vlen l2 then
      lemma_varint_weak_safe b1 b2



let lemma_varint_inv (b:bytes) (n:nat62) (suff:bytes) : Lemma
  (requires S.length b > 0 /\ parse_varint b = Some (n,suff))
  (ensures S.equal b S.(encode_varint n @| suff)) =
  lemma_varint n suff;
  lemma_varint_safe b S.(encode_varint n @| suff)



(*
   +-+-+-+-+-+-+-+-+
   |1|1| T |R R|P P|
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                         Version (32)                          |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |DCIL(4)|SCIL(4)|
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |               Destination Connection ID (0/32..144)         ...
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                 Source Connection ID (0/32..144)            ...
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                           Length (i)                        ...
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                    Packet Number (8/16/24/32)               ...
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                          Payload                            ...
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

    0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1

   +-+-+-+-+-+-+-+-+
   |0|1|S|R|R|K|P P|
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                Destination Connection ID (0..144)           ...
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                     Packet Number (8/16/24/32)              ...
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                     Protected Payload                       ...
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
*)

let rec to_bitfield (k:nat) (n:nat{n < pow2 k}) : Tot (l:(list bool){List.Tot.length l = k})=
  if k = 0 then [] else
  let b0 = (n % 2) = 1 in
  b0 :: (to_bitfield (k - 1) (n / 2))

let rec of_bitfield (l:list bool) : (n:nat{n < pow2 (List.Tot.length l)}) =
  let open FStar.Mul in
  match l with
  | [] -> 0
  | b :: t -> 2 * (of_bitfield t) + (if b then 1 else 0)

let rec lemma_bitfield (k:nat) (n:nat{n < pow2 k})
  : Lemma (of_bitfield (to_bitfield k n) == n)
  =
  if k = 0 then ()
  else lemma_bitfield (k-1) (n/2)

let rec lemma_bitfield_inv (l:list bool)
  : Lemma (to_bitfield (List.Tot.length l) (of_bitfield l) == l)
  =
  match l with
  | [] -> ()
  | _ :: t ->
    assert (List.Tot.length t = List.Tot.length l - 1);
    lemma_bitfield_inv t


let rec lemma_bitfield_lower_bound (n:nat) (l:list bool) : Lemma
  (requires n < List.Tot.length l /\ List.Tot.index l n)
  (ensures of_bitfield l >= pow2 n) =
  if n = 0 then ()
  else
  match l with
  | [] -> ()
  | _ :: tl -> lemma_bitfield_lower_bound (n-1) tl

let rec lemma_bitfield_zero (l:list bool) : Lemma
  (requires (forall i. ~(List.Tot.index l i)))
  (ensures of_bitfield l = 0) =
  match l with
  | [] -> ()
  | false :: t ->
    assert (forall i. List.Tot.index t i = List.Tot.index l (i+1));
    lemma_bitfield_zero t
  | true :: _ -> assert (List.Tot.index l 0 = true)


let rec lemma_bitfield_upper_bound (n:nat) (l:list bool) : Lemma
  (requires
    n < List.Tot.length l /\
    (forall i. i >= n ==> ~(List.Tot.index l i)))
  (ensures of_bitfield l <= pow2 n - 1) =
  if n = 0 then lemma_bitfield_zero l
  else match l with
  | [] -> ()
  | h :: t ->
    assert (forall i. List.Tot.index t i = List.Tot.index l (i+1));
    lemma_bitfield_upper_bound (n-1) t


type bitfield8 = l:list bool{List.Tot.length l = 8}
let to_bitfield8 (b:byte) : bitfield8 = to_bitfield 8 (U8.v b)
let of_bitfield8 (l:bitfield8) : byte = U8.uint_to_t (of_bitfield l)


let lemma_bitfield8 (l:bitfield8) : Lemma
  (requires True)
  (ensures to_bitfield8 (of_bitfield8 l) == l) =
  lemma_bitfield_inv l

let lemma_to_bitfield8_inj (b1 b2:byte) : Lemma
  (requires to_bitfield8 b1 = to_bitfield8 b2)
  (ensures b1 = b2) =
  lemma_bitfield 8 (U8.v b1);
  lemma_bitfield 8 (U8.v b2)



let to_bitfield2 (n:nat2) = let b0::b1::[] = to_bitfield 2 n in (b0, b1)
let of_bitfield2 (b0, b1) : nat2 = of_bitfield [b0; b1]

let lemma_bitfield2 (n:nat2) : Lemma
  (requires True)
  (ensures of_bitfield2 (to_bitfield2 n) = n) =
  lemma_bitfield 2 n

let lemma_of_bitfield2_inj (b0 b1 b2 b3:bool) : Lemma
  (requires of_bitfield2 (b0,b1) = of_bitfield2 (b2,b3))
  (ensures b0 == b2 /\ b1 == b3) =
  lemma_bitfield_inv [b0;b1];
  lemma_bitfield_inv [b2;b3]


let format_header p pn_len npn =
  let open FStar.Endianness in
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  match p with
  | Short spin phase cid ->
    let l = [pnb0; pnb1; phase; false; false; spin; true; false] in
    let flag = of_bitfield8 (assert_norm(List.Tot.length l == 8); l) in
    S.((S.create 1 flag) @| cid @| npn)
  | Long typ version dcil scil dcid scid plain_len ->
    let _ = assert_norm (max_cipher_length < pow2 62) in
    let (typ0, typ1) = to_bitfield2 typ in
    let l = [pnb0; pnb1; false; false; typ0; typ1; true; true] in
    let flag = of_bitfield8 (assert_norm(List.Tot.length l == 8); l) in
    let clen = S.create 1 U8.(16uy *^ uint_to_t dcil +^ uint_to_t scil) in
    S.((S.create 1 flag) @| (n_to_be 4 version) @| clen
      @| dcid @| scid @| (encode_varint plain_len) @| npn)


// lemma justifying that headers have the same size as their
// encryption (type packet)
let format_header_size h pn_len npn (c:cbytes) : Lemma
  (let l = S.length S.(format_header h pn_len npn @| c) in
  l >= 21 /\ l < pow2 32) =
  ()



/// generic lemmas for sequences

let append_slices1 (#a:eqtype) (s1 s2:S.seq a) : Lemma
  (S.equal s1 (S.slice (S.append s1 s2) 0 (S.length s1))) =
  ()

let append_slices2 (#a:eqtype) (s1 s2:S.seq a) : Lemma
  (Seq.equal s2 (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2))) =
  ()

let append_slices3 (#a:eqtype) (s1 s2:S.seq a) : Lemma
  ( (forall (i:nat) (j:nat).
                i <= j /\ j <= Seq.length s2 ==>
                Seq.equal (Seq.slice s2 i j)
                          (Seq.slice (Seq.append s1 s2) (Seq.length s1 + i) (Seq.length s1 + j)))) =
  ()

let lemma_create_slice b i : Lemma
  (requires S.length b >= i)
  (ensures S.(equal (create 1 (index b i)) (slice b i (i+1)))) =
  ()

let lemma_append_assoc (#a:eqtype) (u v w:S.seq a) : Lemma
  (S.equal S.(u @| v @| w) S.((u @| v) @| w)) =
  ()

let compose_split (#a:eqtype) (b:S.seq a) (i j:nat) : Lemma
  (requires i+j <= S.length b)
  (ensures snd (S.split (snd (S.split b i)) j) = snd (S.split b (i+j))) =
  ()

let add_offset (#a:eqtype) (b:S.seq a) (i:nat) (p1 p2:S.seq a) : Lemma
  (requires i <= S.length b /\ S.slice b i (S.length b) = S.(p1@|p2))
  (ensures (
    assert (S.length S.(p1@|p2) = S.length p1+S.length p2);
    S.slice b (i+S.length p1) (S.length b) = p2)) =
  assert (S.length S.(p1@|p2) = S.length p1+S.length p2);
  append_slices2 p1 p2;
  compose_split b i (S.length p1)

let slice_trans (#a:eqtype) (b:S.seq a) (i j k:nat) : Lemma
  (requires i <= j /\ j <= k /\ k <= S.length b)
  (ensures S.slice b i k = S.(slice b i j @| slice b j k)) =
  S.lemma_split (S.slice b i k) (j-i)



/// flag parsing

// result of a flag parsing
type flag =
  | ShortFlag of nat2 * bool * bool * bytes
  | LongFlag of nat2 * nat2 * bytes

let parse_header_flag (b:bytes) : option flag =
  if S.length b = 0 then None else
  match to_bitfield8 (S.index b 0) with
  | [pn0; pn1; phase; false; false; spin; true; false] ->
    Some (ShortFlag (of_bitfield2 (pn0,pn1), phase, spin, S.slice b 1 (S.length b)))
  | [pn0; pn1; false; false; typ0; typ1; true; true] ->
    Some (LongFlag(of_bitfield2 (pn0,pn1), of_bitfield2 (typ0,typ1), S.slice b 1 (S.length b)))
  | _ -> None


let lemma_parse_header_flag_correct h pn_len npn c : Lemma
  (match parse_header_flag S.(format_header h pn_len npn @| c) with
   | None -> False
   | Some (ShortFlag _) -> Short? h
   | Some (LongFlag _) -> Long? h) =
  let b = S.(format_header h pn_len npn @| c) in
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  match h with
  | Short spin phase cid ->
    let l = [pnb0; pnb1; phase; false; false; spin; true; false] in
    assert_norm(List.Tot.length l == 8);
    assert (S.index b 0 = of_bitfield8 l);
    lemma_bitfield8 l
  | Long typ version dcil scil dcid scid plain_len ->
    let _ = assert_norm (max_cipher_length < pow2 62) in
    let (typ0, typ1) = to_bitfield2 typ in
    let l = [pnb0; pnb1; false; false; typ0; typ1; true; true] in
    assert_norm (List.Tot.length l = 8);
    assert (S.index b 0 = of_bitfield8 l);
    lemma_bitfield8 l


let lemma_parse_short_header_flag_correct h pn_len npn c : Lemma
  (requires Short? h)
  (ensures (
    match parse_header_flag S.(format_header h pn_len npn @| c) with
    | Some (ShortFlag (pnl, phase, spin, rest)) ->
      pnl = pn_len /\
      phase = Short?.phase h /\
      spin = Short?.spin h /\
      rest = S.(Short?.cid h @| npn @| c)
    | _ -> False)) =
  match h with
  | Short spin phase cid ->
    let (pnb0, pnb1) = to_bitfield2 pn_len in
    lemma_bitfield2 pn_len;
    let l = [pnb0; pnb1; phase; false; false; spin; true; false] in
    let flag = of_bitfield8 (assert_norm(List.Tot.length l == 8); l) in
    let b = S.(format_header h pn_len npn @| c) in
    assert (S.index b 0 = flag);
    lemma_bitfield8 l;
    assert (S.equal (S.slice b 1 (S.length b)) S.(cid @| npn @| c))

let lemma_recomp_assoc a b c d e f g h : Lemma
  (S.(equal ((a @| b @| c @| d @| e @| f @| g) @| h) (a @| b @| c @| d @| e @| f @| g @| h))) =
  ()



#push-options "--z3rlimit 30"
let lemma_parse_long_header_flag_correct h pn_len npn c : Lemma
  (requires Long? h)
  (ensures (
    match parse_header_flag S.(format_header h pn_len npn @| c) with
    | Some (LongFlag (pnl,typ,rest)) ->
      assert_norm (max_cipher_length < pow2 62);
      let clen = S.create 1 U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
      pnl = pn_len /\
      typ = Long?.typ h /\
      rest = S.(FStar.Endianness.n_to_be 4 (Long?.version h) @| clen @| (Long?.dcid h) @| (Long?.scid h) @| encode_varint (Long?.len h) @| npn @| c)
    | _ -> False)) =
  let open FStar.Endianness in
  match h with
  | Long typ version dcil scil dcid scid plain_len ->
    let (pn0,pn1) = to_bitfield2 pn_len in
    lemma_bitfield2 pn_len;
    let (typ0,typ1) = to_bitfield2 typ in
    lemma_bitfield2 typ;
    let l = [pn0; pn1; false; false; typ0; typ1; true; true] in
    let flag = of_bitfield8 (assert_norm(List.Tot.length l == 8); l) in
    let b = S.(format_header h pn_len npn @| c) in
    assert (S.index b 0 = flag);
    lemma_bitfield8 l;
    match to_bitfield8 flag with
    | [_; _; false; false; _; _; true; true] ->
      let clen = S.create 1 U8.(16uy *^ uint_to_t dcil +^ uint_to_t scil) in
      lemma_recomp_assoc  S.(create 1 flag) (n_to_be 4 version) clen dcid scid (encode_varint plain_len) npn c;
      assert (S.(equal b (create 1 flag @| n_to_be 4 version @| clen @| dcid @| scid @| encode_varint plain_len @| npn @| c)));
      S.append_slices S.(create 1 flag) S.(n_to_be 4 version @| clen @| dcid @| scid @| encode_varint plain_len @| npn @| c)

#pop-options


let lemma_parse_flag_invert (b:bytes) : Lemma
  (requires S.length b > 0)
  (ensures (
    match parse_header_flag b with
    | None -> True
    | Some (ShortFlag (pnl, phase, spin, _)) ->
      let (pn0,pn1) = to_bitfield2 pnl in
      to_bitfield8 (S.index b 0) = [pn0; pn1; phase; false; false; spin; true; false]
    | Some (LongFlag (pnl, typ, _)) ->
      let (pn0,pn1) = to_bitfield2 pnl in
      let (typ0,typ1) = to_bitfield2 typ in
      to_bitfield8 (S.index b 0) = [pn0; pn1; false; false; typ0; typ1; true; true])) =
  match parse_header_flag b with
  | None -> ()
  | Some (ShortFlag (pnl, _, _, _)) ->
    lemma_bitfield2 pnl;
    begin match to_bitfield8 (S.index b 0) with
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] -> ()
    | _ -> () end
  | Some (LongFlag (pnl, typ, _)) ->
    lemma_bitfield2 pnl;
    lemma_bitfield2 typ;
    begin match to_bitfield8 (S.index b 0) with
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] -> ()
    | _ -> () end



let lemma_parse_header_flag_safe (b1 b2:bytes) : Lemma
  (requires parse_header_flag b1 = parse_header_flag b2)
  (ensures
    parse_header_flag b1 = None \/ b1 = b2) =
  match parse_header_flag b1, parse_header_flag b2 with
  | None, _
  | _, None -> ()
  | Some _, Some _ ->
    lemma_parse_flag_invert b1;
    lemma_parse_flag_invert b2;
    lemma_bitfield 8 (U8.v (S.index b1 0));
    lemma_bitfield 8 (U8.v (S.index b2 0));
    assert (S.index b1 0 = S.index b2 0 /\ S.slice b1 1 (S.length b1) = S.slice b2 1 (S.length b2));
    S.lemma_split b1 1;
    S.lemma_split b2 1;
    lemma_create_slice b1 0;
    lemma_create_slice b2 0


/// additional parsing lemmas when only pn_len needs to be parsed

let lemma_parse_flag_pnlen (l:bitfield8) : Lemma
  (match l with
  | a :: b :: _ -> of_bitfield l % 4 = of_bitfield2 (a,b)) =
  ()

// an additional lemma in cases we want to extract only pn_len
let lemma_parse_header_pnlen h pn_len npn : Lemma
  (U8.v (S.index (format_header h pn_len npn) 0) % 4 = pn_len) =
  let open FStar.Mul in
  let res = format_header h pn_len npn in
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  match h with
  | Short spin phase cid ->
    let l = [pnb0; pnb1; phase; false; false; spin; true; false] in
    assert_norm (List.Tot.length l = 8);
    lemma_parse_short_header_flag_correct h pn_len npn S.empty;
    lemma_bitfield 8 (U8.v (S.index res 0));
    lemma_parse_flag_pnlen l;
    lemma_bitfield2 pn_len
  | Long typ version dcil scil dcid scid plain_len ->
    let _ = assert_norm (max_cipher_length < pow2 62) in
    let (typ0, typ1) = to_bitfield2 typ in
    let l = [pnb0; pnb1; false; false; typ0; typ1; true; true] in
    assert_norm (List.Tot.length l = 8);
    lemma_parse_long_header_flag_correct h pn_len npn S.empty;
    lemma_bitfield 8 (U8.v (S.index res 0));
    lemma_parse_flag_pnlen l;
    lemma_bitfield2 pn_len


/// parsing of the cid in short headers

let parse_short_header_cid (b:bytes) (cid_len:nat4) : option (bytes * bytes) =
  if S.length b < add3 cid_len then None
  else Some (S.slice b 0 (add3 cid_len), S.slice b (add3 cid_len) (S.length b))

let cid_len_real h : Lemma
  (requires Short? h)
  (ensures S.length (Short?.cid h) = add3 (cid_len h)) =
  ()

let lemma_parse_short_header_cid_correct h pn_len npn c : Lemma
  (requires Short? h)
  (ensures (
    parse_short_header_cid S.(Short?.cid h @| npn @| c) (cid_len h) = Some (Short?.cid h, S.(npn @| c)))) =
  cid_len_real h;
  S.append_slices (Short?.cid h) S.(npn @| c)

let lemma_parse_short_header_cid_safe (b1 b2:bytes) (cid_len:nat4) : Lemma
  (requires
    parse_short_header_cid b1 cid_len = parse_short_header_cid b2 cid_len)
  (ensures
    parse_short_header_cid b1 cid_len = None \/ b1 = b2) =
  if S.length b1 >= add3 cid_len && S.length b2 >= add3 cid_len then begin
    S.lemma_split b1 (add3 cid_len);
    S.lemma_split b2 (add3 cid_len)
  end


/// parsing of the npn

let parse_short_header_npn (b:bytes) (pn_len:nat2) : option (bytes * cbytes) =
  let len = 1+pn_len in
  if S.length b - len < max_cipher_length && S.length b - len >= 19 then
    Some (S.slice b 0 len, S.slice b len (S.length b))
  else None


let lemma_parse_short_header_npn_correct h (pn_len:nat2) (npn:lbytes (1+pn_len)) (c:cbytes) : Lemma
  (requires Short? h)
  (ensures parse_short_header_npn S.(npn @| c) pn_len = Some (npn,c)) =
  S.append_slices npn c

let lemma_parse_short_header_npn_safe (b1 b2:bytes) (pn_len:nat2) : Lemma
  (requires
    parse_short_header_npn b1 pn_len = parse_short_header_npn b2 pn_len)
  (ensures parse_short_header_npn b1 pn_len = None \/ b1 = b2) =
  if S.length b1 >= 1+pn_len && S.length b2 >= 1+pn_len then begin
    S.lemma_split b1 (1+pn_len);
    S.lemma_split b2 (1+pn_len)
  end


/// parsing of the version in the long header

let parse_long_header_version b : option (nat32 * bytes) =
  let open FStar.Endianness in
  if S.length b < 4 then None
  else
    let _ = lemma_be_to_n_is_bounded (S.slice b 0 4) in
    Some (be_to_n (S.slice b 0 4), S.slice b 4 (S.length b))

let lemma_parse_long_header_version_correct h npn c : Lemma
  (requires Long? h)
  (ensures (
    assert_norm (max_cipher_length < pow2 62);
    let clen = S.create 1 U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
    let next = S.(clen @| (Long?.dcid h) @| (Long?.scid h) @| encode_varint (Long?.len h) @| npn @| c) in
    let input =  S.(FStar.Endianness.n_to_be 4 (Long?.version h) @| next) in
    parse_long_header_version input = Some (Long?.version h, next))) =
   assert_norm (max_cipher_length < pow2 62);
   let clen = S.create 1 U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
   let next = S.(clen @| Long?.dcid h @| Long?.scid h @| encode_varint (Long?.len h) @| npn @| c) in
  S.append_slices (FStar.Endianness.n_to_be 4 (Long?.version h)) next

let lemma_parse_long_header_version_safe b1 b2 : Lemma
  (requires parse_long_header_version b1 = parse_long_header_version b2)
  (ensures parse_long_header_version b1 = None \/ b1 = b2) =
  if S.length b1 >= 4 && S.length b2 >= 4 then begin
    let open FStar.Endianness in
    be_to_n_inj (S.slice b1 0 4) (S.slice b2 0 4);
    S.lemma_split b1 4;
    S.lemma_split b2 4
  end


/// parsing of the clen in the long header

let parse_long_header_clen b : option (nat4 * nat4 * bytes) =
  if S.length b = 0 then None
  else
    let clen = U8.v (S.index b 0) in
    let dcil, scil = clen / 0x10, clen % 0x10 in
    Some (dcil, scil, S.slice b 1 (S.length b))

let lemma_parse_long_header_clen_correct_generic h next : Lemma
  (requires Long? h)
  (ensures (
    assert_norm (max_cipher_length < pow2 62);
    let clen = U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
    let input =  S.(create 1 clen @| next) in
    parse_long_header_clen input = Some (Long?.dcil h, Long?.scil h,next))) =
  assert_norm (max_cipher_length < pow2 62);
  let clen = U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
  let input = S.(create 1 clen @| next) in
  lemma_create_slice input 0;
  S.append_slices S.(create 1 clen) next

let lemma_parse_long_header_clen_correct h npn c : Lemma
  (requires Long? h)
  (ensures (
    assert_norm (max_cipher_length < pow2 62);
    let clen = U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
    let next = S.(Long?.dcid h @| Long?.scid h @| encode_varint (Long?.len h) @| npn @| c) in
    let input =  S.(create 1 clen @| next) in
    parse_long_header_clen input = Some (Long?.dcil h, Long?.scil h,next))) =
  assert_norm (max_cipher_length < pow2 62);
  let clen = U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
  let next = S.(Long?.dcid h @| Long?.scid h @| encode_varint (Long?.len h) @| npn @| c) in
  lemma_parse_long_header_clen_correct_generic h next






let lemma_parse_long_header_clen_safe b1 b2 : Lemma
  (requires parse_long_header_clen b1 = parse_long_header_clen b2)
  (ensures parse_long_header_clen b1 = None \/ b1 = b2) =
  match parse_long_header_clen b1, parse_long_header_clen b2 with
  | None, _
  | _, None -> ()
  | Some _, Some _ ->
    S.lemma_split b1 1;
    S.lemma_split b2 1;
    lemma_create_slice b1 0;
    lemma_create_slice b2 0




/// parsing connection ids

let parse_long_header_id b len : option (qbytes len * bytes) =
  if S.length b < add3 len then None
  else Some (S.slice b 0 (add3 len), S.slice b (add3 len) (S.length b))

let parse_long_header_id_safe b1 b2 len : Lemma
  (requires parse_long_header_id b1 len = parse_long_header_id b2 len)
  (ensures parse_long_header_id b1 len = None \/ b1 = b2) =
  if S.length b1 < add3 len || S.length b2 < add3 len then ()
  else begin
    S.lemma_split b1 (add3 len);
    S.lemma_split b2 (add3 len)
  end

let parse_long_header_dcid_scid b dcil scil : option (qbytes dcil * qbytes scil * bytes) =
  match parse_long_header_id b dcil with
  | None -> None
  | Some (dcid, scid_rest) ->
    match parse_long_header_id scid_rest scil with
    | None -> None
    | Some (scid, rest) -> Some (dcid, scid, rest)

let lemma_parse_long_header_dcid_scid_correct h npn c : Lemma
  (requires Long? h)
  (ensures (
    assert_norm (max_cipher_length < pow2 62);
    let next = S.(encode_varint (Long?.len h) @| npn @| c) in
    let input = S.(Long?.dcid h @| Long?.scid h @| next) in
    parse_long_header_dcid_scid input (Long?.dcil h) (Long?.scil h) = Some (Long?.dcid h, Long?.scid h, next))) =
  assert_norm (max_cipher_length < pow2 62);
  let next = S.(encode_varint (Long?.len h) @| npn @| c) in
  let input = S.(Long?.dcid h @| Long?.scid h @| next) in
  match parse_long_header_id input (Long?.dcil h) with
  | Some (_, scid_rest) ->
    match parse_long_header_id scid_rest (Long?.scil h) with
    | Some _ ->
      S.append_slices (Long?.dcid h) S.(Long?.scid h @| next);
      S.append_slices (Long?.scid h) next

let lemma_parse_long_header_dcid_scid_safe b1 b2 dcil scil : Lemma
  (requires parse_long_header_dcid_scid b1 dcil scil = parse_long_header_dcid_scid b2 dcil scil)
  (ensures parse_long_header_dcid_scid b1 dcil scil = None \/ b1 = b2) =
  match parse_long_header_id b1 dcil, parse_long_header_id b2 dcil with
  | None, _
  | _, None -> ()
  | Some (_, scid_rest1), Some (_, scid_rest2) ->
    match parse_long_header_id scid_rest1 scil, parse_long_header_id scid_rest2 scil with
    | None, _
    | _, None -> ()
    | Some _, Some _ ->
      parse_long_header_id_safe scid_rest1 scid_rest2 scil;
      parse_long_header_id_safe b1 b2 dcil




/// parsing of npn and the suffix

let parse_long_header_npn (l:nat62) (pn_len:nat2) (b:bytes) : option (bytes * cbytes) =
  if 19 <= l && l < max_cipher_length && S.length b = pn_len+1+l then
     Some (S.slice b 0 (pn_len + 1), S.slice b (pn_len + 1) (S.length b))
  else None

let lemma_parse_long_header_npn_correct (h:header) (pn_len:nat2) (npn:lbytes (1+pn_len)) (c:cbytes) : Lemma
  (requires Long? h)
  (ensures (
    assert_norm (max_cipher_length < pow2 62);
    parse_long_header_npn (S.length c) pn_len S.(npn @| c) = Some (npn,c))) =
  assert_norm (max_cipher_length < pow2 62);
  let input = S.(npn @| c) in
  if 19 <= S.length c && S.length c < max_cipher_length && S.length input = pn_len+1+S.length c then begin
    S.append_slices npn c;
    assert (S.length npn = pn_len+1);
    assert (S.slice input 0 (pn_len+1) = npn);
    assert (S.slice input (pn_len+1) (S.length input) = c);
    assert (parse_long_header_npn (S.length c) pn_len S.(npn @| c) = Some (npn,c))
  end

let lemma_parse_long_header_npn_safe (l:nat62) (pn_len:nat2) b1 b2 : Lemma
  (requires parse_long_header_npn l pn_len b1 = parse_long_header_npn l pn_len b2)
  (ensures parse_long_header_npn l pn_len b1 = None \/ b1 = b2) =
  if 19 <= l && l < max_cipher_length && S.length b1 = pn_len+1+l && S.length b2 = pn_len+1+l then begin
    S.lemma_split b1 (1+pn_len);
    S.lemma_split b2 (1+pn_len)
  end





/// compiling all chunks

let parse_header b cid_len =
  match parse_header_flag b with
  | None -> H_Failure
  | Some (ShortFlag (pn_len, phase, spin, rest1)) ->
    begin match parse_short_header_cid rest1 cid_len with
    | None -> H_Failure
    | Some (cid, rest2) ->
      match parse_short_header_npn rest2 pn_len with
      | None -> H_Failure
      | Some (npn,c) -> H_Success pn_len npn (Short spin phase cid) c
    end
  | Some (LongFlag (pn_len, typ, rest1)) ->
    match parse_long_header_version rest1 with
    | None -> H_Failure
    | Some (version, rest2) ->
      match parse_long_header_clen rest2 with
      | None -> H_Failure
      | Some (dcil, scil, rest3) ->
        match parse_long_header_dcid_scid rest3 dcil scil with
        | None -> H_Failure
        | Some (dcid, scid, rest4) ->
          match parse_varint rest4 with
          | None -> H_Failure
          | Some (l, rest5) ->
            match parse_long_header_npn l pn_len rest5 with
            | None -> H_Failure
            | Some (npn,c) ->
              H_Success pn_len npn (Long typ version dcil scil dcid scid l) c



/// proof of correctness
let lemma_header_parsing_correct h pn_len npn c =
  let b = S.(format_header h pn_len npn @| c) in
  lemma_parse_header_flag_correct h pn_len npn c;
  match parse_header_flag b with
  | Some (ShortFlag _) ->
    lemma_parse_short_header_flag_correct h pn_len npn c;
    lemma_parse_short_header_cid_correct h pn_len npn c;
    lemma_parse_short_header_npn_correct h pn_len npn c
  | Some (LongFlag _) ->
    lemma_parse_long_header_flag_correct h pn_len npn c;
    lemma_parse_long_header_version_correct h npn c;
    lemma_parse_long_header_clen_correct h npn c;
    lemma_parse_long_header_dcid_scid_correct h npn c;
    assert_norm (max_cipher_length < pow2 62);
    lemma_varint (Long?.len h) S.(npn @| c);
    lemma_parse_long_header_npn_correct h pn_len npn c



/// proof of safety

type parsed_short_flag b =
  (let res = parse_header_flag b in
  Some? res /\ ShortFlag? (Some?.v res))
type parsed_long_flag b =
  (let res = parse_header_flag b in
  Some? res /\ LongFlag? (Some?.v res))
let failure_parse b cid_len =
  H_Failure? (parse_header b cid_len)

// case 1: two short headers
let lemma_header_parsing_safe_short_short b1 b2 cid_len : Lemma
  (requires
    parsed_short_flag b1 /\
    parsed_short_flag b2 /\
    parse_header b1 cid_len = parse_header b2 cid_len)
  (ensures failure_parse b1 cid_len \/ b1 = b2) =
  match parse_header_flag b1, parse_header_flag b2 with
  | Some (ShortFlag (pn_len1, _, _, r1)),
    Some (ShortFlag (pn_len2, _, _, s1)) ->
    match parse_short_header_cid r1 cid_len,
          parse_short_header_cid s1 cid_len with
  | None, _
  | _, None -> ()
  | Some (_,r2), Some (_,s2) ->
    match parse_short_header_npn r2 pn_len1,
          parse_short_header_npn s2 pn_len2 with
    | None, _
    | _, None -> ()
    | Some _, Some _ ->
      lemma_parse_short_header_npn_safe r2 s2 pn_len1;
      lemma_parse_short_header_cid_safe r1 s1 cid_len;
      lemma_parse_header_flag_safe b1 b2

// case 2: two long headers
let lemma_header_parsing_safe_long_long b1 b2 cid_len : Lemma
  (requires
    parsed_long_flag b1 /\
    parsed_long_flag b2 /\
    parse_header b1 cid_len = parse_header b2 cid_len)
  (ensures failure_parse b1 cid_len \/ b1 = b2) =
  match parse_header_flag b1, parse_header_flag b2 with
  | Some (LongFlag (pn_len1, typ1, r1)),
    Some (LongFlag (pn_len2, typ2, s1)) ->
    match parse_long_header_version r1, parse_long_header_version s1 with
    | None, _ | _, None -> ()
    | Some (version1, r2), Some (version2, s2) ->
      match parse_long_header_clen r2,parse_long_header_clen s2 with
      | None, _ | _, None -> ()
      | Some (dcil1, scil1, r3), Some (dcil2, scil2, s3) ->
        match parse_long_header_dcid_scid r3 dcil1 scil1, parse_long_header_dcid_scid s3 dcil2 scil2 with
        | None, _ | _, None -> ()
        | Some (dcid1, scid1, r4), Some (dcid2, scid2, s4) ->
          match parse_varint r4, parse_varint s4 with
          | None, _ | _, None  -> ()
          | Some (l1, r5), Some (l2, s5) ->
            match parse_long_header_npn l1 pn_len1 r5, parse_long_header_npn l2 pn_len2 s5 with
            | None, _ | _, None -> ()
            | Some _, Some _ ->
              lemma_parse_long_header_npn_safe l1 pn_len1 r5 s5;
              lemma_varint_safe r4 s4;
              lemma_parse_long_header_dcid_scid_safe r3 s3 dcil1 scil1;
              lemma_parse_long_header_clen_safe r2 s2;
              lemma_parse_long_header_version_safe r1 s1;
              lemma_parse_header_flag_safe b1 b2

// case 3: incompatible-type headers
let lemma_result_parse_short_header b cid_len : Lemma
  (requires parsed_short_flag b)
  (ensures
    failure_parse b cid_len \/
    Short? (H_Success?.h (parse_header b cid_len))) =
  ()

let lemma_result_parse_long_header b cid_len : Lemma
  (requires parsed_long_flag b)
  (ensures
    failure_parse b cid_len \/
    Long? (H_Success?.h (parse_header b cid_len))) =
  ()

let lemma_incompatibility_short_long b1 b2 cid_len : Lemma
  (requires parsed_short_flag b1 /\ parsed_long_flag b2)
  (ensures
    failure_parse b1 cid_len \/
    failure_parse b2 cid_len \/
    parse_header b1 cid_len <> parse_header b2 cid_len) =
  lemma_result_parse_short_header b1 cid_len;
  lemma_result_parse_long_header b2 cid_len



let lemma_header_parsing_safe b1 b2 cid_len =
  match parse_header_flag b1, parse_header_flag b2 with
  | None, _
  | _, None -> ()
  | Some (ShortFlag _), Some (ShortFlag _) ->
    lemma_header_parsing_safe_short_short b1 b2 cid_len
  | Some (LongFlag _), Some (LongFlag _) ->
    lemma_header_parsing_safe_long_long b1 b2 cid_len
  | Some (ShortFlag _), Some (LongFlag _) ->
    lemma_incompatibility_short_long b1 b2 cid_len
  | Some (LongFlag _), Some (ShortFlag _) ->
    lemma_incompatibility_short_long b2 b1 cid_len



// application of a byte operation at a subposition
let rec pointwise_op (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (pos:nat) : Pure (S.seq a)
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
  (decreases (S.length b2)) =
  if b2 = S.empty then b1
  else
    let _ = S.lemma_empty b2 in
    let x = f (S.index b1 pos) (S.index b2 0) in
    pointwise_op f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) (pos + 1)


// three lemmas to recover indexes after application of bitwise_op
let rec pointwise_index1 (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (i pos:nat) : Lemma
  (requires (S.length b2 + pos <= S.length b1 /\ i < pos))
  (ensures (S.index (pointwise_op f b1 b2 pos) i = S.index b1 i))
  (decreases (S.length b2)) =
  if b2 = S.empty then ()
  else begin
    S.lemma_empty b2;
    let x = f (S.index b1 pos) (S.index b2 0) in
    assert (pointwise_op f b1 b2 pos = pointwise_op f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) (pos + 1));
    S.lemma_index_upd2 b1 pos x i;
    assert (S.index (S.upd b1 pos x) i = S.index b1 i);
    pointwise_index1 f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) i (pos + 1)
  end


let rec pointwise_index2 (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (i pos:nat) : Lemma
  (requires (S.length b2 + pos <= S.length b1 /\ pos <= i /\ i < S.length b2 + pos))
  (ensures (S.index (pointwise_op f b1 b2 pos) i = f (S.index b1 i) (S.index b2 (i-pos))))
  (decreases (S.length b2)) =
  if S.empty = b2 then ()
  else begin
    let x = f (S.index b1 pos) (S.index b2 0) in
    assert (pointwise_op f b1 b2 pos = pointwise_op f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) (pos+1));
    if i = pos then begin
      pointwise_index1 f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) pos (pos+1);
      S.lemma_index_upd1 b1 pos x
    end
    else
      pointwise_index2 f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) i (pos+1)
  end


let rec pointwise_index3 (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (i pos:nat) : Lemma
  (requires (S.length b2 + pos <= i /\ i < S.length b1))
  (ensures (S.index (pointwise_op f b1 b2 pos) i = S.index b1 i))
  (decreases (S.length b2)) =
  if S.empty = b2 then ()
  else begin
    S.lemma_empty b2;
    let x = f (S.index b1 pos) (S.index b2 0) in
    pointwise_index3 f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) i (pos+1)
  end





// application: byte-wise xor
let rec xor_inplace (b1 b2:bytes) (pos:nat)
  : Pure bytes
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
  (decreases (S.length b2)) =
  pointwise_op U8.logxor b1 b2 pos


// proof of involution of the operator (uses extensionality for the
// byte-wise variant)
let xor_involutive (b1 b2:byte) : Lemma
  (requires True)
  (ensures (b1 `U8.logxor` b2) `U8.logxor` b2 = b1) =
  FStar.UInt.logxor_associative (U8.v b1) (U8.v b2) (U8.v b2);
  FStar.UInt.logxor_self (U8.v b2);
  FStar.UInt.logxor_commutative (FStar.UInt.zero 8) (U8.v b1);
  FStar.UInt.logxor_lemma_1 (U8.v b1)


let rec xor_inplace_involutive (b1 b2:bytes) (pos:nat) : Lemma
  (requires S.length b2 + pos <= S.length b1)
  (ensures S.equal (xor_inplace (xor_inplace b1 b2 pos) b2 pos) b1)
  (decreases (S.length b2)) =
  let xor = xor_inplace (xor_inplace b1 b2 pos) b2 pos in
  let step (i:nat{i < S.length b1}) : Lemma (S.index xor i = S.index b1 i) =
    if i < pos then begin
      pointwise_index1 U8.logxor b1 b2 i pos;
      pointwise_index1 U8.logxor (xor_inplace b1 b2 pos) b2 i pos
    end else if i >= pos+S.length b2 then begin
      pointwise_index3 U8.logxor b1 b2 i pos;
      pointwise_index3 U8.logxor (xor_inplace b1 b2 pos) b2 i pos
    end else begin
      pointwise_index2 U8.logxor b1 b2 i pos;
      pointwise_index2 U8.logxor (xor_inplace b1 b2 pos) b2 i pos;
      xor_involutive  (S.index b1 i) (S.index b2 (i-pos))
    end in

  FStar.Classical.forall_intro step



let rec and_inplace (b1 b2:bytes) (pos:nat)
  : Pure bytes
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
  (decreases (S.length b2)) =
  pointwise_op U8.logand b1 b2 pos



let calg_of_ae (a:ea) = match a with
| AEAD.AES128_GCM -> C16.AES128
| AEAD.AES256_GCM -> C16.AES256
| AEAD.CHACHA20_POLY1305 -> C16.CHACHA20

let lemma_format_len (a:ea) (h:header) (pn_len:nat2) (npn:lbytes (1+pn_len))
  : Lemma (S.length (format_header h pn_len npn) <= AEAD.max_length a)
  = assert_norm(54 < pow2 32 - 70)

(*
Constant time decryption of packet number (without branching on pn_len)
packet[pn_offset..pn_offset+4] ^= pn_mask &
  match pn_len with
  | 0 -> mask & 0xFF000000
  | 1 -> mask & 0xFFFF0000
  | 2 -> mask & 0xFFFFFF00
  | 3 -> mask & 0xFFFFFFFF
*)
inline_for_extraction private
let pn_sizemask (pn_len:nat2) : lbytes 4 =
  let open FStar.Endianness in
  n_to_be 4 (pow2 32 - pow2 (24 - (8 `op_Multiply` pn_len)))

let header_encrypt a hpk h pn_len npn c =
  assert_norm(max_cipher_length < pow2 62);
  let pn_offset = match h with
    | Short _ _ cid -> 1 + S.length cid
    | Long _ _ dcil scil _ _ pl -> 6 + add3 dcil + add3 scil + vlen pl in
  let sample = S.slice c (3-pn_len) (19-pn_len) in
  let mask = C16.block (calg_of_ae a) hpk sample in
  let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
  let sflags = if Short? h then 0x1fuy else 0x0fuy in
  let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
  let r = S.(format_header h pn_len npn @| c) in
  let r = xor_inplace r pnmask pn_offset in
  let r = xor_inplace r fmask 0 in
  r




let header_decrypt a hpk cid_len packet =
  let open FStar.Math.Lemmas in
  let f = S.index packet 0 in
  let is_short = U8.(f <^ 128uy) in
  (* See https://tools.ietf.org/html/draft-ietf-quic-tls-19#section-5.4.2 *)
  let sample_offset =
    if is_short then
      let offset = 5 + add3 cid_len in
      if offset + 16 <= S.length packet then
        Some (S.slice packet offset (offset+16), offset-4)
      else None
    else
      let (dcil,scil,rest) = Some?.v (parse_long_header_clen (S.slice packet 5 (S.length packet))) in
      let l_offset = 6 + add3 dcil + add3 scil in
      match parse_varint rest with
      | None -> None
      | Some (len, npn_c) ->
        let pn_offset = l_offset + vlen len in
        if pn_offset + 20 <= S.length packet then
           Some (S.slice npn_c 4 20, pn_offset)
        else None in
  match sample_offset with
  | None -> H_Failure
  | Some (sample,pn_offset) ->
    //let sample = S.slice packet so (so + 16) in
    let mask = C16.block (calg_of_ae a) hpk sample in
    let sflags = if is_short then 0x1fuy else 0x0fuy in
    let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
    let packet' = xor_inplace packet fmask 0 in
    let flags = U8.v (S.index packet' 0) in
    let pn_len : nat2 = modulo_range_lemma flags 4; flags % 4 in
    let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
    //let pn_offset = so - 4 in
    let packet'' = xor_inplace packet' pnmask pn_offset in
    parse_header packet'' cid_len



// manipulation of bitfield as lists
let lemma_bitfield8_128_aux (l:bitfield8) : Lemma
  (U8.(of_bitfield8 l >=^ 128uy) <==> List.Tot.index l 7) =
  if List.Tot.index l 7 then lemma_bitfield_lower_bound 7 l
  else lemma_bitfield_upper_bound 7 l

let lemma_bitfield8_128 (b:byte) : Lemma
  (U8.(b >=^ 128uy) <==> List.Tot.index (to_bitfield8 b) 7) =
  lemma_bitfield8_128_aux (to_bitfield8 b);
  lemma_bitfield 8 (U8.v b)


let max (a b:nat) : Tot (n:nat{n >= a /\ n >= b}) =
  if a > b then a else b // this must exist somewhere...


let rec bitwise_op (f:bool->bool->bool) (l1 l2:list bool) : Pure (list bool)
  (requires List.Tot.length l1 = List.Tot.length l2)
  (ensures fun l -> List.Tot.length l = List.Tot.length l1) =
  match l1,l2 with
  | [],[] -> []
  | x1::t1,x2::t2 -> f x1 x2 :: bitwise_op f t1 t2


let rec lemma_bitwise_op_index (f:bool->bool->bool) (l1 l2:list bool) (n:nat) : Lemma
  (requires List.Tot.length l1 = List.Tot.length l2 /\ n < List.Tot.length l1)
  (ensures List.Tot.index (bitwise_op f l1 l2) n = f (List.Tot.index l1 n) (List.Tot.index l2 n)) =
  match l1,l2 with
  | [],[] -> ()
  | x1::t1,x2::t2 ->
    if n = 0 then ()
    else lemma_bitwise_op_index f t1 t2 (n-1)




// characterisation of logand in terms of bitfields
let lemma_charac_logand (n:pos) (b1 b2:FStar.UInt.uint_t n) : Lemma
  (requires True)
  (ensures (
    let open FStar.BitVector in
    let open FStar.UInt in
    let l1 = to_bitfield n b1 in
    let l2 = to_bitfield n b2 in
    let vb1 = to_vec #n b1 in
    let vb2 = to_vec #n b2 in
    S.equal (logand_vec vb1 vb2)
    (to_vec #n (of_bitfield (bitwise_op (fun x y -> x && y) l1 l2))))) =
  let open FStar.BitVector in
  let open FStar.UInt in
  let l1 = to_bitfield n b1 in
  let l2 = to_bitfield n b2 in
  let vb1 = to_vec #n b1 in
  let vb2 = to_vec #n b2 in
  let right = to_vec #n (of_bitfield (bitwise_op (fun x y -> x && y) l1 l2)) in

  let index_right i : Lemma
    (S.index right i = (S.index vb1 i && S.index vb2 i)) =
    admit() in

  FStar.Classical.forall_intro index_right


let lemma_charac_logand_byte (b1 b2:byte) : Lemma
  (requires True)
  (ensures (
    let l1 = to_bitfield8 b1 in
    let l2 = to_bitfield8 b2 in
    to_bitfield8 U8.(b1 `logand` b2) =
    bitwise_op (fun x y -> x && y) l1 l2)) =
  let l1 = to_bitfield8 b1 in
  let l2 = to_bitfield8 b2 in
  let l = bitwise_op (fun x y -> x && y) l1 l2 in
  lemma_charac_logand 8 (U8.v b1) (U8.v b2);
  assert (of_bitfield8 l = U8.(b1 `logand` b2));
  lemma_bitfield_inv (bitwise_op (fun x y -> x && y) l1 l2)



// characterisation of logxor as bitfields. Code duplication from
// the logxor characterisation.
let lemma_charac_logxor (n:pos) (b1 b2:FStar.UInt.uint_t n) : Lemma
  (requires True)
  (ensures (
    let open FStar.BitVector in
    let open FStar.UInt in
    let l1 = to_bitfield n b1 in
    let l2 = to_bitfield n b2 in
    let vb1 = to_vec #n b1 in
    let vb2 = to_vec #n b2 in
    S.equal (logxor_vec vb1 vb2)
    (to_vec #n (of_bitfield (bitwise_op (fun x y -> x <> y) l1 l2))))) =
  let open FStar.BitVector in
  let open FStar.UInt in
  let l1 = to_bitfield n b1 in
  let l2 = to_bitfield n b2 in
  let vb1 = to_vec #n b1 in
  let vb2 = to_vec #n b2 in
  let right = to_vec #n (of_bitfield (bitwise_op (fun x y -> x <> y) l1 l2)) in

  let index_right i : Lemma
    (S.index right i = (S.index vb1 i <> S.index vb2 i)) =
    admit() in

  FStar.Classical.forall_intro index_right



let lemma_charac_logxor_byte (b1 b2:byte) : Lemma
  (requires True)
  (ensures (
    let l1 = to_bitfield8 b1 in
    let l2 = to_bitfield8 b2 in
    to_bitfield8 U8.(b1 `logxor` b2) =
    bitwise_op (fun x y -> x <> y) l1 l2)) =
  let l1 = to_bitfield8 b1 in
  let l2 = to_bitfield8 b2 in
  let l = bitwise_op (fun x y -> x <> y) l1 l2 in
  lemma_charac_logxor 8 (U8.v b1) (U8.v b2);
  assert (of_bitfield8 l = U8.(b1 `logxor` b2));
  lemma_bitfield_inv (bitwise_op (fun x y -> x <> y) l1 l2)






// extraction of a type of a header
let lemma_index_list_7 (l:bitfield8) : Lemma
  (match l with _ :: _ :: _ :: _ :: _ :: _ :: _ :: x :: _ ->
    List.Tot.index l 7 = x) =
  ()



let lemma_header_type_128 p pn_len npn : Lemma
  (Short? p <==> U8.(S.index (format_header p pn_len npn) 0 <^ 128uy)) =
  let b = format_header p pn_len npn in
  if Short? p then begin
    lemma_parse_short_header_flag_correct p pn_len npn S.empty;
    let l = to_bitfield8 (S.index b 0) in
    assert_norm (List.Tot.length l = 8);
    lemma_bitfield8_128 (S.index b 0);
    lemma_index_list_7 l;
    assert (List.Tot.index l 7 = false)
  end
  else begin
    lemma_parse_long_header_flag_correct p pn_len npn S.empty;
    let l = to_bitfield8 (S.index b 0) in
    assert_norm (List.Tot.length l = 8);
    lemma_bitfield8_128 (S.index b 0);
    lemma_index_list_7 l;
    assert (List.Tot.index l 7 = true)
  end




// correctness of the condition to check whether a header is short
let lemma_header_encrypt_type_short a hpk h pn_len npn c : Lemma
  (requires (
    let packet = header_encrypt a hpk h pn_len npn c in
    U8.(S.index packet 0 <^ 128uy)))
  (ensures Short? h) =
  if Short? h then ()
  else begin

    // notations
    assert_norm(max_cipher_length < pow2 62);
    let pn_offset =
      match h with
      | Long _ _ dcil scil _ _ pl -> 6 + add3 dcil + add3 scil + vlen pl in
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let mask = C16.block (calg_of_ae a) hpk sample in
    let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
    let sflags = 0x0fuy in
    let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
    let r1 = S.(format_header h pn_len npn @| c) in
    let r2 = xor_inplace r1 pnmask pn_offset in
    let packet = xor_inplace r2 fmask 0 in

    // proving that the most significant bit of fmask is 0
    let sflags_bitfield = to_bitfield8 sflags in
    assert_norm (~(List.Tot.index sflags_bitfield 7));
    let fmask_bitfield = to_bitfield8 (S.index fmask 0) in
    lemma_charac_logand_byte (S.index mask 0) sflags;
    lemma_bitwise_op_index (fun x y -> x && y) (to_bitfield8 (S.index mask 0)) (to_bitfield8 sflags) 7;

    // extracting the flags from the cipher
    pointwise_index1 U8.logxor r1 pnmask 0 pn_offset;
    pointwise_index2 U8.logxor r2 fmask 0 0;
    lemma_charac_logxor_byte (S.index r1 0) (S.index fmask 0);
    let r1_bitfield = to_bitfield8 (S.index (format_header h pn_len npn) 0) in

    // extracting the last bit
    lemma_bitwise_op_index (fun x y -> x <> y) r1_bitfield fmask_bitfield 7;
    lemma_bitfield8_128 (S.index packet 0);
    lemma_bitfield8_128 (S.index (format_header h pn_len npn) 0);
    lemma_header_type_128 h pn_len npn
  end



// same, for the long header. Proof is duplicated, except for the
// definition of pn_offset and sflags
let lemma_header_encrypt_type_long a hpk h pn_len npn c : Lemma
  (requires (
    let packet = header_encrypt a hpk h pn_len npn c in
    U8.(S.index packet 0 >=^ 128uy)))
  (ensures (Long? h)) =
  if Long? h then ()
  else begin

    // notations
    assert_norm(max_cipher_length < pow2 62);
    let pn_offset =
      match h with
      | Short _ _ cid -> 1 + S.length cid in
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let mask = C16.block (calg_of_ae a) hpk sample in
    let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
    let sflags = 0x1fuy in
    let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
    let r1 = S.(format_header h pn_len npn @| c) in
    let r2 = xor_inplace r1  pnmask pn_offset in
    let packet = xor_inplace r2 fmask 0 in

    // proving that the most significant bit of fmask is 0
    let sflags_bitfield = to_bitfield8 sflags in
    assert_norm (~(List.Tot.index sflags_bitfield 7));
    let fmask_bitfield = to_bitfield8 (S.index fmask 0) in
    lemma_charac_logand_byte (S.index mask 0) sflags;
    lemma_bitwise_op_index (fun x y -> x && y) (to_bitfield8 (S.index mask 0)) (to_bitfield8 sflags) 7;

    // extracting the flags from the cipher
    pointwise_index1 U8.logxor r1 pnmask 0 pn_offset;
    pointwise_index2 U8.logxor r2 fmask 0 0;
    lemma_charac_logxor_byte (S.index r1 0) (S.index fmask 0);
    let r1_bitfield = to_bitfield8 (S.index (format_header h pn_len npn) 0) in

    // extracting the last bit
    lemma_bitwise_op_index (fun x y -> x <> y) r1_bitfield fmask_bitfield 7;
    lemma_bitfield8_128 (S.index packet 0);
    lemma_bitfield8_128 (S.index (format_header h pn_len npn) 0);
    lemma_header_type_128 h pn_len npn
  end



let lemma_header_encrypt_type a hpk h pn_len npn c : Lemma
  (let packet = header_encrypt a hpk h pn_len npn c in
  U8.(S.index packet 0 <^ 128uy) <==> Short? h) =
  let packet = header_encrypt a hpk h pn_len npn c in
  if U8.(S.index packet 0 <^ 128uy) then
    lemma_header_encrypt_type_short a hpk h pn_len npn c
  else lemma_header_encrypt_type_long a hpk h pn_len npn c



type header_encryption_correct
  (a:ea)
  (k:lbytes (ae_keysize a))
  (h: header)
  (pn_len: nat2)
  (npn: lbytes (1+pn_len))
  (c: cbytes)
  = (header_decrypt a k (cid_len h)
    (header_encrypt a k h pn_len npn c)
    == H_Success pn_len npn h c)



let lemma_arithmetic1 (a b c d e:int) : Lemma
  ((a+b+c+d)+(e-d) = (a+c+e)+b) =
  ()

let lemma_arithmetic2 (a b c d:int) : Lemma
  (a+(b-c)+d = a + ((b+d)-c)) =
  ()

let lemma_arithmetic3 (a b c:int) : Lemma
  ((a+b)-c = (a-c)+b) =
  ()




let lemma_header_encryption_short_sample a k h pn_len npn c : Lemma
  (requires Short? h)
  (ensures (
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let packet = header_encrypt a k h pn_len npn c in
    let so = 5 + add3 (cid_len h) in
    sample = S.slice packet so (so+16))) =

  // computation of the packet
  let pn_offset = 1 + S.length (Short?.cid h) in
  let sample = S.slice c (3-pn_len) (19-pn_len) in
  let mask = C16.block (calg_of_ae a) k sample in
  let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
  let sflags = 0x1fuy in
  let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
  let r1 = S.(format_header h pn_len npn @| c) in
  let r2 = xor_inplace r1 pnmask pn_offset in
  let r = xor_inplace r2 fmask 0 in

  // comparison of the offsets
  let so = 5 + S.length (Short?.cid h) in
  cid_len_real h;

  // extraction of the sample
  let index_beyond_so (i:nat{i >= so /\ i < S.length r1}) : Lemma
    (S.index r i = S.index r1 i) =
    pointwise_index3 U8.logxor r1 pnmask i pn_offset;
    pointwise_index3 U8.logxor r2 fmask i 0 in

  FStar.Classical.forall_intro index_beyond_so;
  assert (S.equal (S.slice r so (so+16)) (S.slice r1 so (so+16)));
  assert_norm (pn_offset = 1 + S.length (Short?.cid h));
  assert_norm (so = 5 + S.length (Short?.cid h));

  assert (S.length (format_header h pn_len npn) = 1 + S.length (Short?.cid h) + 1 + pn_len);
  lemma_arithmetic1 1 (S.length (Short?.cid h)) 1 pn_len 3;
  assert (so = S.length (format_header h pn_len npn) + (3-pn_len));
  lemma_arithmetic2 (S.length (format_header h pn_len npn)) 3 pn_len 16;
  assert (so+16 = S.length (format_header h pn_len npn) + (19-pn_len));
  append_slices3 (format_header h pn_len npn) c





let lemma_header_encryption_correct_short a k h pn_len npn c : Lemma
  (requires Short? h)
  (ensures header_encryption_correct a k h pn_len npn c) =

  // computing the result of header_encrypt
  let pn_offset = 1 + S.length (Short?.cid h) in
  let sample = S.slice c (3-pn_len) (19-pn_len) in
  let mask = C16.block (calg_of_ae a) k sample in
  let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
  let sflags = 0x1fuy in
  let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
  let r1 = S.(format_header h pn_len npn @| c) in
  let r2 = xor_inplace r1 pnmask pn_offset in
  let packet = xor_inplace r2 fmask 0 in
  assert (packet = header_encrypt a k h pn_len npn c);

  // proving that the decryption extracts correctly the header type
  let f = S.index packet 0 in
  lemma_header_encrypt_type a k h pn_len npn c;
  let is_short = U8.(f <^ 128uy) in
  assert (is_short);

  // extraction of the sample
  let sample_offset : option (n:nat{n+16 <= S.length packet}) =
    let offset = 5 + add3 (cid_len h) in
    if offset + 16 <= S.length packet then Some offset else None in

  match sample_offset with
  | None -> ()
  | Some so ->
    cid_len_real h;
    lemma_header_encryption_short_sample a k h pn_len npn c;

    // removing the fmask
    let packet' = xor_inplace packet fmask 0 in
    xor_inplace_involutive r2 fmask 0;
    // computing pn_len
    let flags = U8.v (S.index packet' 0) in
    pointwise_index1 U8.logxor r1 pnmask 0 pn_offset;
    lemma_parse_header_pnlen h pn_len npn;
    // computing pn_offset
    lemma_arithmetic3 5 (S.length (Short?.cid h)) 4;
    // removing the pnmask
    let packet'' = xor_inplace packet' pnmask pn_offset in
    xor_inplace_involutive r1 pnmask pn_offset;
    // parsing the header
    lemma_header_parsing_correct h pn_len npn c




/// correctness of decryption for long headers

let long_header_npn_offset (h:header) : Pure nat
  (requires Long? h)
  (ensures fun _ -> True) =
  assert_norm (max_cipher_length < pow2 62);
  6 + add3 (Long?.dcil h) + add3 (Long?.scil h) + vlen (Long?.len h)

let lemma_long_header_npn_offset h pn_len npn c : Lemma
  (requires Long? h)
  (ensures (
    let open S in
    assert_norm (max_cipher_length < pow2 62);
    let b = format_header h pn_len npn @| c in
    let offset = long_header_npn_offset h in
    equal (npn @| c) (slice b offset (S.length b)))) =
  let open S in
  let b = format_header h pn_len npn @| c in
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  let (typ0, typ1) = to_bitfield2 (Long?.typ h) in
  let l = [pnb0; pnb1; false; false; typ0; typ1; true; true] in
  assert_norm (List.Tot.length l = 8);
  let flag = create 1 (of_bitfield8 l) in
  let version = FStar.Endianness.n_to_be 4 (Long?.version h) in
  let clen = S.create 1 U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
  let dcid = Long?.dcid h in
  let scid = Long?.scid h in
  assert_norm (max_cipher_length < pow2 62);
  let plain_len = encode_varint (Long?.len h) in
  lemma_recomp_assoc flag version clen dcid scid plain_len npn c;
  assert (equal (slice b 0 (length b)) (flag @| version @| clen @| dcid @| scid @| plain_len @| npn @| c));
  add_offset b 0 flag (version @| clen @| dcid @| scid @| plain_len @| npn @| c);
  add_offset b 1 version (clen @| dcid @| scid @| plain_len @| npn @| c);
  add_offset b 5 clen (dcid @| scid @| plain_len @| npn @| c);
  add_offset b 6 dcid (scid @| plain_len @| npn @| c);
  add_offset b (6 + add3 (Long?.dcil h)) scid (plain_len @| npn @| c);
  add_offset b (6 + add3 (Long?.dcil h) + add3 (Long?.scil h)) plain_len (npn @| c)


let lemma_long_header_clen_offset h pn_len npn c b : Lemma
  (requires (
    let res = S.(format_header h pn_len npn @| c) in
    Long? h /\
    S.length b = S.length res /\
    S.index b 5 = S.index res 5))
  (ensures (
    let next = S.slice b 6 (S.length b) in
    let input = S.slice b 5 (S.length b) in
    parse_long_header_clen input = Some (Long?.dcil h, Long?.scil h,next))) =
  let open FStar.Endianness in
  let open S in
  let res = S.(format_header h pn_len npn @| c) in
  assert_norm (max_cipher_length < pow2 62);
  let clen = U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
  lemma_parse_long_header_flag_correct h pn_len npn c;
  add_offset res 1 (n_to_be 4 (Long?.version h)) (create 1 clen @| Long?.dcid h @| Long?.scid h @| encode_varint (Long?.len h) @| npn @| c);
  assert (index res 5 = index (slice res 5 (length res)) 0);
  slice_trans b 5 6 (length b);
  lemma_create_slice b 5;
  lemma_parse_long_header_clen_correct_generic h (slice b 6 (length b))


#push-options "--z3rlimit 30"
let lemma_long_header_plen_offset (h:header) (pn_len:nat2) (npn:lbytes (1+pn_len)) (c:cbytes) (b:bytes) : Lemma
  (requires
    Long? h /\ (
    assert_norm (max_cipher_length < pow2 62);
    let res = S.(format_header h pn_len npn @| c) in
    let offset = 6 + add3 (Long?.dcil h) + add3 (Long?.scil h) in
    let vl = vlen (Long?.len h) in
    S.length b = S.length res /\
    S.equal (S.slice b offset (offset+vl)) (S.slice res offset (offset+vl))))
  (ensures (
    let offset = 6 + add3 (Long?.dcil h) + add3 (Long?.scil h) in
    match parse_varint (S.slice b offset (S.length b)) with
    | None -> False
    | Some (_,rest) -> S.equal rest (S.slice b (long_header_npn_offset h) (S.length b)))) =
  let open FStar.Endianness in
  let open S in
  let res = S.(format_header h pn_len npn @| c) in
  assert_norm (max_cipher_length < pow2 62);
  let clen = U8.(16uy *^ uint_to_t (Long?.dcil h) +^ uint_to_t (Long?.scil h)) in
  lemma_parse_long_header_flag_correct h pn_len npn c;
  add_offset res 1 (n_to_be 4 (Long?.version h)) (create 1 clen @| Long?.dcid h @| Long?.scid h @| encode_varint (Long?.len h) @| npn @| c);
  add_offset res 5 (create 1 clen) (Long?.dcid h @| Long?.scid h @| encode_varint (Long?.len h) @| npn @| c);
  add_offset res 6 (Long?.dcid h) (Long?.scid h @| encode_varint (Long?.len h) @| npn @| c);
  add_offset res (6+add3 (Long?.dcil h)) (Long?.scid h) (encode_varint (Long?.len h) @| npn @| c);
  let pre_offset = 6 + add3 (Long?.dcil h) + add3 (Long?.scil h) in
  let offset = long_header_npn_offset h in
  add_offset res pre_offset (encode_varint (Long?.len h)) (npn @| c);
  append_slices1 (encode_varint (Long?.len h)) (npn @| c);
  assert (S.slice res pre_offset offset = encode_varint (Long?.len h));
  assert (S.slice b pre_offset offset = encode_varint (Long?.len h));
  lemma_varint (Long?.len h) (S.slice b offset (S.length b));
  slice_trans b pre_offset offset (S.length b)

#pop-options

let long_sample (packet:packet) : option bytes =
  let (dcil,scil,rest) = Some?.v (parse_long_header_clen (S.slice packet 5 (S.length packet))) in
  match parse_varint rest with
  | None -> None
  | Some (len, npn_c) ->
    let pn_offset = 6 + add3 dcil + add3 scil + vlen len in
    if pn_offset + 20 <= S.length packet then
       Some (S.slice npn_c 4 20)
    else None


let lemma_header_encryption_long_sample a k h pn_len npn c : Lemma
  (requires Long? h)
  (ensures (
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let packet = header_encrypt a k h pn_len npn c in
    match long_sample packet with
    | None -> False
    | Some s -> S.equal sample s)) =

  // computation of the packet
  assert_norm(max_cipher_length < pow2 62);
  let pn_offset = 6 + add3 (Long?.dcil h) + add3 (Long?.scil h) + vlen (Long?.len h) in
  let sample = S.slice c (3-pn_len) (19-pn_len) in
  let mask = C16.block (calg_of_ae a) k sample in
  let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
  let sflags = 0x0fuy in
  let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
  let r1 = S.(format_header h pn_len npn @| c) in
  let r2 = xor_inplace r1 pnmask pn_offset in
  let packet = xor_inplace r2 fmask 0 in

  // computation of the sample
  let (dcil,scil,rest) = Some?.v (parse_long_header_clen (S.slice packet 5 (S.length packet))) in
  pointwise_index3 U8.logxor r2 fmask 5 0;
  pointwise_index1 U8.logxor r1 pnmask 5 pn_offset;
  lemma_long_header_clen_offset h pn_len npn c packet;

  let preserve_plen (i:nat{let offset = 6 + add3 (Long?.dcil h) + add3 (Long?.scil h) in let vl = vlen (Long?.len h) in offset <= i /\ i < offset+vl}) : Lemma
    (S.index packet i = S.index r1 i) =
    pointwise_index3 U8.logxor r2 fmask i 0;
    pointwise_index1 U8.logxor r1 pnmask i pn_offset in

  FStar.Classical.forall_intro preserve_plen;
  lemma_long_header_plen_offset h pn_len npn c packet;
  //match parse_varint rest with
 admit()


let lemma_header_encryption_long_sample a k h pn_len npn c : Lemma
  (requires Long? h)
  (ensures (
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let packet = header_encrypt a k h pn_len npn c in
    match long_sample_offset packet with
    | None -> False
    | Some so -> S.equal sample (S.slice packet so (so+16)))) =

  // computation of the packet
  assert_norm(max_cipher_length < pow2 62);
  let pn_offset = 6 + add3 (Long?.dcil h) + add3 (Long?.scil h) + vlen (Long?.len h) in
  let sample = S.slice c (3-pn_len) (19-pn_len) in
  let mask = C16.block (calg_of_ae a) k sample in
  let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
  let sflags = 0x0fuy in
  let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
  let r1 = S.(format_header h pn_len npn @| c) in
  let r2 = xor_inplace r1 pnmask pn_offset in
  let r = xor_inplace r2 fmask 0 in

  admit();
  // comparison of the offsets
  let so = 5 + S.length (Short?.cid h) in
  cid_len_real h;

  // extraction of the sample
  let index_beyond_so (i:nat{i >= so /\ i < S.length r1}) : Lemma
    (S.index r i = S.index r1 i) =
    pointwise_index3 U8.logxor r1 pnmask i pn_offset;
    pointwise_index3 U8.logxor r2 fmask i 0 in

  FStar.Classical.forall_intro index_beyond_so;
  assert (S.equal (S.slice r so (so+16)) (S.slice r1 so (so+16)));
  assert_norm (pn_offset = 1 + S.length (Short?.cid h));
  assert_norm (so = 5 + S.length (Short?.cid h));

  assert (S.length (format_header h pn_len npn) = 1 + S.length (Short?.cid h) + 1 + pn_len);
  lemma_arithmetic1 1 (S.length (Short?.cid h)) 1 pn_len 3;
  assert (so = S.length (format_header h pn_len npn) + (3-pn_len));
  lemma_arithmetic2 (S.length (format_header h pn_len npn)) 3 pn_len 16;
  assert (so+16 = S.length (format_header h pn_len npn) + (19-pn_len));
  append_slices3 (format_header h pn_len npn) c



let lemma_header_encryption_correct_long a k h pn_len npn c : Lemma
  (requires Long? h)
  (ensures header_encryption_correct a k h pn_len npn c) =

  // computing the result of header_encrypt
  assert_norm(max_cipher_length < pow2 62);
  let pn_offset = 6 + add3 (Long?.dcil h) + add3 (Long?.scil h) + vlen (Long?.len h) in
  let sample = S.slice c (3-pn_len) (19-pn_len) in
  let mask = C16.block (calg_of_ae a) k sample in
  let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
  let sflags = 0x0fuy in
  let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
  let r1 = S.(format_header h pn_len npn @| c) in
  let r2 = xor_inplace r1 pnmask pn_offset in
  let packet = xor_inplace r2 fmask 0 in
  assert (packet = header_encrypt a k h pn_len npn c);

  // proving that the decryption extracts correctly the header type
  let f = S.index packet 0 in
  lemma_header_encrypt_type a k h pn_len npn c;
  let is_short = U8.(f <^ 128uy) in
  assert (~is_short);

  // extraction of the sample
  let sample_offset : option (n:nat{n+16 <= S.length packet}) =
     let dcb = U8.v (S.index packet 5) in
     let dcil, scil = dcb / 0x10, dcb % 0x10 in
     let _ = FStar.Math.Lemmas.modulo_range_lemma dcb 0x10 in
     let l_offset = 6 + add3 dcil + add3 scil in
     (if l_offset >= S.length packet then None else
     match parse_varint (S.slice packet l_offset (S.length packet)) with
     | None -> None
     | Some (l, _) ->
       let offset = l_offset + vlen l + 4 in
       if offset + 16 <= S.length packet then Some offset else None)
    in

  lemma_header_encryption_long_sample a k h pn_len npn c;
  match sample_offset with
  | None -> ()
  | Some so ->
    assert (S.equal sample (S.slice packet so (so+16)));

    // removing the fmask
    let packet' = xor_inplace packet fmask 0 in
    xor_inplace_involutive r2 fmask 0;
    assert (packet' = r2);
    // computing pn_len
    let flags = U8.v (S.index packet' 0) in
    pointwise_index1 U8.logxor r1 pnmask 0 pn_offset;
    assert (flags = U8.v (S.index (format_header h pn_len npn) 0));
    lemma_parse_header_pnlen h pn_len npn;
    assert (pn_len = flags % 4); admit();
    // computing pn_offset
    admit();
    //lemma_arithmetic3 5 (S.length (Short?.cid h)) 4;
    assert (pn_offset = so - 4);
    // removing the pnmask
    let packet'' = xor_inplace packet' pnmask pn_offset in
    xor_inplace_involutive r1 pnmask pn_offset;
    assert (packet'' = r1);
    // parsing the header
    lemma_header_parsing_correct h pn_len npn c







let lemma_header_encryption_correct a k h pn_len npn c : Lemma
  (header_encryption_correct a k h pn_len npn c) =
  if Short? h then
    lemma_header_encryption_correct_short a k h pn_len npn c
  else lemma_header_encryption_correct_long a k h pn_len npn c



let lemma_header_encryption_malleable a k c spin phase cid x npn = admit()

let coerce (#a:Type) (x:a) (b:Type) : Pure b
  (requires a == b) (ensures fun y -> y == x) = x

inline_for_extraction private
let hide (x:bytes) : Pure (S.seq Lib.IntTypes.uint8)
  (requires True) (ensures fun r -> S.length x == S.length r)
  = S.init (S.length x) (fun i -> Lib.IntTypes.secret #Lib.IntTypes.U8 (S.index x i))

inline_for_extraction private
let reveal (x:S.seq Lib.IntTypes.uint8) : Pure bytes
  (requires True) (ensures fun r -> S.length x == S.length r)
  = S.init (S.length x) (fun i -> U8.uint_to_t (Lib.IntTypes.uint_v (S.index x i)))

#push-options "--z3rlimit 30"
let encrypt a k siv hpk pn_len seqn h plain =
  let open FStar.Endianness in
  assert_norm(8 `op_Multiply` 12 == 96);
  assert_norm(pow2 62 < pow2 96 /\ pow2 16 < pow2 62 /\ 54 < max_plain_length);
  let pnb = n_to_be 12 seqn in
  let npn : lbytes (1+pn_len) = S.slice pnb (11 - pn_len) 12 in
  let header = format_header h pn_len npn in 
  lemma_format_len a h pn_len npn;
  let iv = xor_inplace pnb siv 0 in
  let cipher = AEAD.encrypt #a (hide k) (hide iv) (hide header) (hide plain) in
  header_encrypt a hpk h pn_len npn (reveal cipher)
#pop-options

#push-options "--z3rlimit 20"
let lemma_disjoint_sum (k:nat) (a:nat) (b:nat) (u:nat)
  : Lemma (requires a < pow2 k /\ a % pow2 u == 0 /\ b < pow2 u /\ u < k)
  (ensures a + b < pow2 k) =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  lemma_div_mod a (pow2 u);
  assert(a + b == pow2 u * (a / pow2 u) + b);
  lemma_div_plus b (a / pow2 u) (pow2 u);
  small_div b (pow2 u);
  lemma_div_lt_nat a k u;
  assert((a / pow2 u) < pow2 (k-u));
  assert(((a + b) / pow2 u) / pow2 (k-u) < 1);
  division_multiplication_lemma (a+b) (pow2 u) (pow2 (k-u));
  pow2_plus u (k-u); ()
#pop-options

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-20#appendix-A *)
#push-options "--z3rlimit 20"
let expand_npn (last:nat{last + 1 < pow2 62}) (pn_len:nat2) (npn:nat{npn < pow2 (8 `op_Multiply` (pn_len + 1))}) : n:nat{n < pow2 62} =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  let bits = 8 * (pn_len + 1) in
  assert(pn_len < 4 /\ bits < 33);
  let wbits = bits - 1 in
  let hlast = ((last + 1) / pow2 bits) in
  lemma_div_lt (last+1) 62 bits;
  assert(hlast < pow2 (62 - bits));
  assert(pow2 bits * hlast < pow2 bits * pow2 (62 - bits));
  pow2_plus bits (62-bits);
  let high = pow2 bits * hlast in
  assert(high < pow2 62);
  lemma_mod_plus 0 hlast (pow2 bits);
  assert(high % pow2 bits == 0);
  let candidate = npn + high in
  lemma_disjoint_sum 62 high npn bits;
  assert(candidate < pow2 62);
  if candidate + pow2 wbits <= last + 1  then
    candidate + pow2 wbits
  else if candidate - pow2 wbits > last + 1 && candidate > pow2 bits then
    candidate - pow2 wbits
  else candidate
#pop-options

#push-options "--z3rlimit 30 --admit_smt_queries true"
let decrypt a k siv hpk last cid_len packet =
  let open FStar.Math.Lemmas in
  let open FStar.Endianness in
  match header_decrypt a hpk cid_len packet with 
  | H_Failure -> Failure
  | H_Success pn_len npn h c ->
    let pn = expand_npn last pn_len (be_to_n npn) in
    let pnb = n_to_be 12 pn in
    let iv = xor_inplace pnb siv 0 in
    let aad = format_header h pn_len npn in
    match AEAD.decrypt #a (hide k) (hide pnb) (hide aad) (hide c) with
    | None -> Failure
    | Some plain -> Success pn_len pn h (reveal plain)
#pop-options

let lemma_encrypt_correct a k siv hpk pn_len pn h p = admit()
