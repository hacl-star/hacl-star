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

let parse_varint_suffixless (b:bytes{S.length b > 0}) : option (n:nat{n < pow2 62} * vlsize) =
  let open FStar.Endianness in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  assert_norm(pow2 8 / 0x40 == 4);
  assert_norm(0x4000 < pow2 62 /\ 0x40000000 < pow2 62 /\ 0x4000000000000000 == pow2 62);
  // b0 is the integer interpretation of the first 2 bits of b
  let b0 = U8.v (S.index b 0) / 0x40 in
  let n = be_to_n b in
  if S.length b < pow2 b0 then None else
  (match b0 with
  | 0 -> Some (n % 0x40, 1)
  | 1 -> Some (n % 0x4000, 2)
  | 2 -> Some (n % 0x40000000, 4)
  | 3 -> Some (n % 0x4000000000000000, 8))


let parse_varint (b:bytes{S.length b > 0}) : option (n:nat{n < pow2 62} * vlsize) =
  let open FStar.Endianness in
  // b0 is the integer interpretation of the first 2 bits of b
  let b0 = U8.v (S.index b 0) / 0x40 in
  if S.length b < pow2 b0 then None
  else parse_varint_suffixless (S.slice b 0 (pow2 b0))


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

#push-options "--z3rlimit 40"
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

private let lemma_varint_case1 (n:nat{n < pow2 14})
  : Lemma (parse_varint_suffixless (FStar.Endianness.n_to_be 2 (pow2 14 + n)) ==
    Some (mod_case1 n, 2))
  =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  let b = n_to_be 2 (pow2 14 + n) in
  let b0 = U8.v (S.index b 0) / 0x40 in
  let n' = be_to_n b in
  lemma_be_index 2 (pow2 14 + n);
  division_multiplication_lemma (pow2 14 + n) 0x100 0x40;
  lemma_divrem2 14 14 n;
  assert(S.length b == 2 /\ b0 == 1 /\ n % 0x4000 == n);
  match b0 with
  | 1 -> assert(parse_varint b == Some (n % 0x4000, 2))

private let mod_case2 (n:nat) : n:nat{n < pow2 62} =
  let open FStar.Math.Lemmas in
  assert_norm(0x40000000 < pow2 62);
  modulo_range_lemma n 0x40000000; n % 0x40000000

private let lemma_varint_case2 (n:nat{n < pow2 30})
  : Lemma (parse_varint_suffixless (FStar.Endianness.n_to_be 4 (pow2 31 + n)) ==
    Some (mod_case2 n, 4)) =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  let b = n_to_be 4 (pow2 31 + n) in
  let b0 = U8.v (S.index b 0) / 0x40 in
  let n' = be_to_n b in
  lemma_be_index 4 (pow2 31 + n);
  division_multiplication_lemma (pow2 31 + n) 0x1000000 0x40;
  lemma_divrem2 30 31 n;
  assert(S.length b == 4 /\ b0 == 2 /\ n % 0x40000000 == n);
  match b0 with
  | 2 -> assert(parse_varint b == Some (n % 0x40000000, 4))

private let mod_case3 (n:nat) : n:nat{n < pow2 62} =
  let open FStar.Math.Lemmas in
  assert_norm(0x4000000000000000 == pow2 62);
  modulo_range_lemma n 0x4000000000000000; n % 0x4000000000000000

let lemma_varint_case3 (n:nat{n < pow2 62})
  : Lemma (parse_varint (FStar.Endianness.n_to_be 8 (pow2 63 + pow2 62 + n)) ==
    Some (mod_case3 n, 8)) =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  assert_norm(pow2 (8 * 0) == 1 /\ pow2 (8 * 1) == 0x100 /\ pow2 (8 * 3) == 0x1000000 /\ pow2 (8 * 7) == 0x100000000000000);
  let b = n_to_be 8 (pow2 63 + pow2 62 + n) in
  let b0 = U8.v (S.index b 0) / 0x40 in
  let n' = be_to_n b in
  lemma_be_index 8 (pow2 63 + pow2 62 + n);
  division_multiplication_lemma (pow2 63 + pow2 62 + n) 0x100000000000000 0x40;
  lemma_divrem3 62 63 62 n;
  match b0 with
  | 3 -> assert(parse_varint b == Some (n % 0x4000000000000000, 8))

#push-options "--z3rlimit 20"

let lemma_varint_suffixless (n:nat62) : Lemma
  (parse_varint (encode_varint n) == Some (n, vlen n)) =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  assert_norm(pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 8 == 256);
  assert_norm(pow2 8 / 0x40 == 4);
  assert_norm(0x4000 < pow2 62 /\ 0x40000000 < pow2 62 /\ 0x4000000000000000 == pow2 62);
  assert_norm(pow2 6 == 0x40 /\ pow2 14 == 0x4000 /\ pow2 30 == 0x40000000 /\ pow2 62 == 0x4000000000000000);
  assert_norm(pow2 (8 * 0) == 1 /\ pow2 (8 * 1) == 0x100 /\ pow2 (8 * 3) == 0x1000000 /\ pow2 (8 * 7) == 0x100000000000000);
  assert_norm(0x100 * 0x40 == 0x4000 /\ 0x1000000 * 0x40 == 0x40000000);
  let b = encode_varint n in
  let b0 = U8.v (S.index b 0) / 0x40 in
  let n' = be_to_n b in
  let k = S.length b in
  if n < pow2 6 then
   begin
    lemma_be_index 1 n;
    small_div n (pow2 6); small_mod n (pow2 6);
    S.lemma_empty (suffix b 1);
    match b0 with
    | 0 -> assert(parse_varint b == Some (n' % 0x40, 1))
   end
  else if n < pow2 14 then lemma_varint_case1 n
  else if n < pow2 30 then lemma_varint_case2 n
  else lemma_varint_case3 n


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


let lemma_varint (suff:bytes) (n:nat62) : Lemma
  (parse_varint S.(encode_varint n @| suff) == Some (n, vlen n)) =
  let b = encode_varint n in
  let b0 = U8.v (S.index b 0) / 0x40 in
  length_encode n;
  assert (S.length b = pow2 b0);
  assert (parse_varint S.(b @| suff) = parse_varint_suffixless (S.slice S.(b @| suff) 0 (pow2 b0)));
  S.append_slices b suff;
  assert (S.slice S.(b @| suff) 0 (S.length b) = b);
  assert (parse_varint S.(b @| suff) = parse_varint_suffixless b);
  lemma_varint_suffixless n





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

let rec to_bitfield (k:nat) (n:nat{n < pow2 k}) =
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
  | _ :: t -> lemma_bitfield_inv t


let to_bitfield8 (b:byte) = to_bitfield 8 (U8.v b)
let of_bitfield8 (l:list bool{List.Tot.length l == 8}) : byte = U8.uint_to_t (of_bitfield l)


let lemma_bitfield8 (l:list bool{List.Tot.length l == 8}) : Lemma
  (requires True)
  (ensures to_bitfield8 (of_bitfield8 l) == l) =
  lemma_bitfield_inv l



let to_bitfield2 (n:nat2) = let b0::b1::[] = to_bitfield 2 n in (b0, b1)
let of_bitfield2 (b0, b1) : nat2 = of_bitfield [b0; b1]

let lemma_bitfield2 (n:nat2) : Lemma
  (requires True)
  (ensures of_bitfield2 (to_bitfield2 n) = n) =
  lemma_bitfield 2 n



let format_header p pn_len npn =
  let open FStar.Endianness in
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  match p with
  | Short spin phase cid ->
    let l = [pnb0; pnb1; phase; false; false; spin; true; false] in
    let flag = of_bitfield8 (assert_norm(List.Tot.length l == 8); l) in
    S.((S.create 1 flag) @| cid @| npn)
  | Long typ version dcil scil dcid scid plain_len ->
    let _ = assert_norm (max_plain_length < pow2 62) in
    let (typ0, typ1) = to_bitfield2 typ in
    let l = [pnb0; pnb1; false; false; typ0; typ1; true; true] in
    let flag = of_bitfield8 (assert_norm(List.Tot.length l == 8); l) in
    let clen = S.create 1 U8.(16uy *^ uint_to_t dcil +^ uint_to_t scil) in
    S.((S.create 1 flag) @| (n_to_be 4 version) @| clen
      @| dcid @| scid @| (encode_varint plain_len) @| npn)




let parse_header b cid_len =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  if S.length b = 0 then H_Failure
  else
    match to_bitfield8 (S.index b 0) with
    | [pn0; pn1; phase; false; false; spin; true; false] ->
      let pn_len : nat2 = of_bitfield2 (pn0, pn1) in
      let len = 1 + (add3 cid_len) + 1 + pn_len in
      if S.length b = len then
        let npn = S.slice b (1 + add3 cid_len) len in
	let cid = S.slice b 1 (1 + add3 cid_len) in
        H_Success pn_len npn (Short spin phase cid)
      else H_Failure
    | [pn0; pn1; false; false; typ0; typ1; true; true] ->
      let pn_len : nat2 = of_bitfield2 (pn0, pn1) in
      let typ = of_bitfield2 (typ0, typ1) in
      if S.length b >= 6 then
        let _ = lemma_be_to_n_is_bounded (S.slice b 1 5) in
        let version : nat32 = be_to_n (S.slice b 1 5) in
	let cl = U8.v (S.index b 5) in
        let _ = modulo_range_lemma cl 0x10 in
        let dcil, scil : nat4 * nat4 = cl / 0x10, cl % 0x10 in
	let pos_length = 6 + add3 dcil + add3 scil in
	if S.length b >= pos_length + 1 then
	  let dcid = S.slice b 6 (6 + add3 dcil) in
	  let scid = S.slice b (6 + add3 dcil) (6 + add3 dcil + add3 scil) in
	  match parse_varint (S.slice b pos_length (S.length b)) with
	  | Some (l, vll) ->
	    let pos_pn = pos_length + vll in
	    if S.length b = pos_pn + pn_len + 1 && l <= max_plain_length then
	      let npn = S.slice b pos_pn (pos_pn + pn_len + 1) in
	      H_Success pn_len npn (Long typ version dcil scil dcid scid l)
	    else H_Failure
	  | None -> H_Failure
	else H_Failure
      else H_Failure
    | _ -> H_Failure




/// Todo HERE

let extract_dcil_scil (dcil:nat4) (scil:nat4) (cl:nat) : Lemma
  (requires (let open FStar.Mul in cl = 0x10 * dcil + scil))
  (ensures (cl % 0x10 = scil /\ cl / 0x10 = dcil)) =
  ()


let size_long_header_bound_cid p pn_len npn : Lemma
  (requires True)
  (ensures S.length (format_header p pn_len npn) >= 1 + add3 (Long?.dcil p) + add3 (Long?.scil p)) =
  ()


type parsing_correct h pn_len npn =
  parse_header (format_header h pn_len npn) (cid_len h) == H_Success pn_len npn h

let lemma_short_header_parsing_correct h pn_len npn : Lemma
  (requires (Short? h))
  (ensures (parsing_correct h pn_len npn)) =
  let b = format_header h pn_len npn in
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  lemma_bitfield2 pn_len;
  if S.length b <> 0 then
    match h with
    | Short spin phase cid ->
      let l = [pnb0;pnb1; phase; false; false; spin; true; false] in
      assert_norm(List.Tot.length l == 8);
      lemma_bitfield8 l;
      assert (to_bitfield8 (S.index b 0) == l);
      let flag = of_bitfield8 l in
      let len = 1 + (add3 (cid_len h)) + 1 + pn_len in
      if S.length b = len then begin
        S.append_slices (S.create 1 flag) (S.append cid npn);
        S.append_slices cid npn;
        assert (S.slice b (1+add3 (cid_len h)) len = npn);
        assert (S.slice b 1 (1 + add3 (cid_len h)) = cid);
        assert (parse_header b (cid_len h) = H_Success pn_len npn h)
      end
    | _ -> ()



#push-options "--z3rlimit 20"

let lemma_long_header_parsing_correct_flag h pn_len npn : Lemma
  (requires Long? h)
  (ensures (
    let b = format_header h pn_len npn in
    let (pnb0, pnb1) = to_bitfield2 pn_len in
    let (typ0, typ1) = to_bitfield2 (Long?.typ h) in
    let l = [pnb0; pnb1; false; false; typ0; typ1; true; true] in
    to_bitfield8 (S.index b 0) = l)) =
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  lemma_bitfield2 pn_len;
  match h with
  | Long typ _ _ _ _ _ _ ->
    let (typ0, typ1) = to_bitfield2 typ in
    let l = [pnb0; pnb1; false; false; typ0; typ1; true; true] in
    assert_norm(List.Tot.length l == 8);
    lemma_bitfield8 l

#pop-options



// Splitting the lemma S.append_slices in several parts. This is
// dirty, but otherwise the SMT solver is lost after ~4 applications
// of the lemma (and here we need 7)
let append_slices1 (s1:bytes) (s2:bytes) : Lemma
  (S.equal s1 (S.slice (S.append s1 s2) 0 (S.length s1))) =
  ()

let append_slices3 (s1:bytes) (s2:bytes) : Lemma
  ( (forall (i:nat) (j:nat).
                i <= j /\ j <= Seq.length s2 ==>
                Seq.equal (Seq.slice s2 i j)
                          (Seq.slice (Seq.append s1 s2) (Seq.length s1 + i) (Seq.length s1 + j)))) =
  ()


// lemmas about recovery of appended components using S.slice
let lemma_slice_long_header1 (u1 u2 u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures (
    let b = S.(u1 @| u2 @| u3 @| u4 @| u5 @| u6 @| u7) in
    u1 = S.slice b 0 (S.length u1))) =
  append_slices1 u1 S.(u2 @| u3 @| u4 @| u5 @| u6 @| u7)

let lemma_slice_long_header2 (u1 u2 u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures (
    let b = S.(u1 @| u2 @| u3 @| u4 @| u5 @| u6 @| u7) in
    u2 = S.slice b (S.length u1) (S.length u1+S.length u2))) =
  append_slices1 u2 S.(u3 @| u4 @| u5 @| u6 @| u7);
  append_slices3 u1 S.(u2 @| u3 @| u4 @| u5 @| u6 @| u7)


let lemma_slice_long_header3 (u1 u2 u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures (
    let b = S.(u1 @| u2 @| u3 @| u4 @| u5 @| u6 @| u7) in
    u3 = S.slice b (S.length u1+S.length u2) (S.length u1+S.length u2+S.length u3))) =
  append_slices1 u3 S.(u4 @| u5 @| u6 @| u7);
  append_slices3 u2 S.(u3 @| u4 @| u5 @| u6 @| u7);
  append_slices3 u1 S.(u2 @| u3 @| u4 @| u5 @| u6 @| u7)

let lemma_slice_long_header4 (u1 u2 u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures (
    let b = S.(u1 @| u2 @| u3 @| u4 @| u5 @| u6 @| u7) in
    u4 = S.slice b (S.length u1+S.length u2+S.length u3) (S.length u1+S.length u2+S.length u3+S.length u4))) =
  append_slices1 u4 S.(u5 @| u6 @| u7);
  append_slices3 u3 S.(u4 @| u5 @| u6 @| u7);
  append_slices3 u2 S.(u3 @| u4 @| u5 @| u6 @| u7);
  append_slices3 u1 S.(u2 @| u3 @| u4 @| u5 @| u6 @| u7)

let lemma_slice_long_header5 (u1 u2 u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures (
    let b = S.(u1 @| u2 @| u3 @| u4 @| u5 @| u6 @| u7) in
    u5 = S.slice b (S.length u1+S.length u2+S.length u3+S.length u4) (S.length u1+S.length u2+S.length u3+S.length u4+S.length u5))) =
  append_slices1 u5 S.(u6 @| u7);
  append_slices3 u4 S.(u5 @| u6 @| u7);
  append_slices3 u3 S.(u4 @| u5 @| u6 @| u7);
  append_slices3 u2 S.(u3 @| u4 @| u5 @| u6 @| u7);
  append_slices3 u1 S.(u2 @| u3 @| u4 @| u5 @| u6 @| u7)

let lemma_slice_long_header6 (u1 u2 u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures (
    let b = S.(u1 @| u2 @| u3 @| u4 @| u5 @| u6 @| u7) in
    u6 = S.slice b (S.length u1+S.length u2+S.length u3+S.length u4+S.length u5) (S.length u1+S.length u2+S.length u3+S.length u4+S.length u5+S.length u6))) =
  append_slices1 u6 u7;
  append_slices3 u5 S.(u6 @| u7);
  append_slices3 u4 S.(u5 @| u6 @| u7);
  append_slices3 u3 S.(u4 @| u5 @| u6 @| u7);
  append_slices3 u2 S.(u3 @| u4 @| u5 @| u6 @| u7);
  append_slices3 u1 S.(u2 @| u3 @| u4 @| u5 @| u6 @| u7)


// not so sure why, but the last iteration is much less automatable
// than the others. Had to decompose it into 7 sublemmas
let lemma_slice_long_header7_step7 (u7:bytes) : Lemma
  (requires True)
  (ensures u7 = S.slice u7 0 (S.length u7)) =
  ()

let lemma_slice_long_header7_step6 (u6 u7:bytes) : Lemma
  (requires True)
  (ensures u7 = S.slice S.(u6 @| u7) (S.length u6) (S.length u6+S.length u7)) =
  lemma_slice_long_header7_step7 u7;
  S.append_slices u6 u7

let lemma_slice_long_header7_step5 (u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures u7 = S.slice S.(u5 @| u6 @| u7) (S.length u5+S.length u6) (S.length u5+S.length u6+S.length u7)) =
  lemma_slice_long_header7_step6 u6 u7;
  S.append_slices u5 S.(u6 @| u7)

let lemma_slice_long_header7_step4 (u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures u7 = S.slice S.(u4 @| u5 @| u6 @| u7) (S.length u4+S.length u5+S.length u6) (S.length u4+S.length u5+S.length u6+S.length u7)) =
  lemma_slice_long_header7_step5 u5 u6 u7;
  S.append_slices u4 S.(u5 @| u6 @| u7)

let lemma_slice_long_header7_step3 (u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures u7 = S.slice S.(u3 @| u4 @| u5 @| u6 @| u7) (S.length u3+S.length u4+S.length u5+S.length u6) (S.length u3+S.length u4+S.length u5+S.length u6+S.length u7)) =
  lemma_slice_long_header7_step4 u4 u5 u6 u7;
  S.append_slices u3 S.(u4 @| u5 @| u6 @| u7)

let lemma_slice_long_header7_step2 (u2 u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures u7 = S.slice S.(u2 @|u3 @| u4 @| u5 @| u6 @| u7) (S.length u2+S.length u3+S.length u4+S.length u5+S.length u6) (S.length u2+S.length u3+S.length u4+S.length u5+S.length u6+S.length u7)) =
  lemma_slice_long_header7_step3 u3 u4 u5 u6 u7;
  S.append_slices u2 S.(u3 @| u4 @| u5 @| u6 @| u7)

let lemma_slice_long_header7 (u1 u2 u3 u4 u5 u6 u7:bytes) : Lemma
  (requires True)
  (ensures (
    let b = S.(u1 @| u2 @|u3 @| u4 @| u5 @| u6 @| u7) in
    u7 = S.slice b (S.length u1+S.length u2+S.length u3+S.length u4+S.length u5+S.length u6) (S.length u1+S.length u2+S.length u3+S.length u4+S.length u5+S.length u6+S.length u7))) =
  lemma_slice_long_header7_step2 u2 u3 u4 u5 u6 u7;
  S.append_slices u1 S.(u2 @| u3 @| u4 @| u5 @| u6 @| u7)


let lemma_slice_long_header67 (u1 u2 u3 u4 u5 u6:bytes) : Lemma
  (requires True)
  (ensures (
    let b = S.(u1 @| u2 @|u3 @| u4 @| u5 @| u6) in
    u6 = S.slice b (S.length u1+S.length u2+S.length u3+S.length u4+S.length u5) (S.length b))) =
  assert (S.equal S.(u1 @| u2 @|u3 @| u4 @| u5 @| u6) S.(u1 @| u2 @|u3 @| u4 @| u5 @| u6 @| empty));
  lemma_slice_long_header6 u1 u2 u3 u4 u5 u6 S.empty


#push-options "--z3rlimit 20"
let lemma_long_header_parsing_correct h pn_len npn : Lemma
  (requires (Long? h))
  (ensures (parsing_correct h pn_len npn)) =
  let b = format_header h pn_len npn in
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  lemma_bitfield2 pn_len;
  if S.length b <> 0 then
    match h with
    | Long typ version dcil scil dcid scid plain_len ->
      let open FStar.Endianness in
      let (typ0, typ1) = to_bitfield2 typ in
      let l = [pnb0; pnb1; false; false; typ0; typ1; true; true] in
      lemma_long_header_parsing_correct_flag h pn_len npn;
      // assert (to_bitfield8 (S.index b 0) = l);
      let flag = of_bitfield8 (assert_norm (List.Tot.length l == 8); l) in
      lemma_bitfield2 typ;
      let cl8 = U8.(16uy *^ uint_to_t dcil +^ uint_to_t scil) in
      let (u1,u2,u3,u4,u5,u6,u7) = (S.create 1 flag, n_to_be 4 version, S.create 1 cl8, dcid, scid, encode_varint (assert_norm(max_plain_length <= pow2 62); plain_len), npn) in
      assert (b = S.(u1 @| u2 @| u3 @| u4 @| u5 @| u6 @| u7));
      if S.length b >= 6 then begin
        // extracting the flag
        lemma_slice_long_header1 u1 u2 u3 u4 u5 u6 u7;
        assert (S.slice b 0 1 = u1);
        // extracting the version
        lemma_slice_long_header2 u1 u2 u3 u4 u5 u6 u7;
        assert (be_to_n (S.slice b 1 5) = version);
        // extracting clen
        lemma_slice_long_header3 u1 u2 u3 u4 u5 u6 u7;
        assert (S.index b 5 = cl8);
        let cl = U8.v cl8 in
        // extracting dci, scil
        extract_dcil_scil dcil scil cl;
        // extracting cid
        let pos_length = 6 + add3 dcil + add3 scil in
        size_long_header_bound_cid h pn_len npn;
        if S.length b >= pos_length + 1 then begin
          // dcid
          lemma_slice_long_header4 u1 u2 u3 u4 u5 u6 u7;
          assert (u4 = S.slice b 6 (6+add3 dcil));
          // scid
          lemma_slice_long_header5 u1 u2 u3 u4 u5 u6 u7;
          assert (u5 = S.slice b (6+add3 dcil) (6+add3 dcil+add3 scil));
          // extracting plain_len
          lemma_slice_long_header67 u1 u2 u3 u4 u5 S.(u6 @| u7);
          assert (S.(u6 @| u7) = S.slice b pos_length (S.length b));
          lemma_varint u7 plain_len;
          assert (parse_varint (S.slice b pos_length (S.length b)) = Some (plain_len, vlen plain_len));
          match parse_varint (S.slice b pos_length (S.length b)) with
          | Some (l, vll) ->
	    let pos_pn = pos_length + vll in
	    if S.length b = pos_pn + pn_len + 1 && l <= max_plain_length then begin
              assert (l = plain_len /\ vll = S.length u6);
              // extracting npn
              lemma_slice_long_header7 u1 u2 u3 u4 u5 u6 u7;
              assert (u7 = S.slice b pos_pn (pos_pn + pn_len + 1));
              assert (parse_header b (cid_len h) = H_Success pn_len npn h)
            end
        end
      end


#pop-options


let lemma_header_parsing_correct h pn_len npn =
  let b = format_header h pn_len npn in
  let (pnb0, pnb1) = to_bitfield2 pn_len in
  lemma_bitfield2 pn_len;
  if S.length b <> 0 then
    match h with
    | Short spin phase cid ->
      lemma_short_header_parsing_correct h pn_len npn
    | Long typ version dcil scil dcid scid plain_len ->
      lemma_long_header_parsing_correct h pn_len npn







let lemma_header_parsing_safe b1 b2 =
  admit()



let rec xor_inplace (b1 b2:bytes) (pos:nat)
  : Pure bytes
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
  (decreases (S.length b2)) =
  if b2 = S.empty then b1
  else
    let _ = S.lemma_empty b2 in
    let x = S.index b2 0 `U8.logxor` S.index b1 pos in
    xor_inplace (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) (pos + 1)

let rec and_inplace (b1 b2:bytes) (pos:nat)
  : Pure bytes
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
  (decreases (S.length b2)) =
  if b2 = S.empty then b1
  else
    let _ = S.lemma_empty b2 in
    let x = S.index b2 0 `U8.logand` S.index b1 pos in
    and_inplace (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) (pos + 1)

let calg_of_ae (a:ea) = match a with
| AEAD.AES128_GCM -> C16.AES128
| AEAD.AES256_GCM -> C16.AES256
| AEAD.CHACHA20_POLY1305 -> C16.CHACHA20

let lemma_format_len (h:header) (pn_len:nat2) (npn:lbytes (1+pn_len))
  : Lemma (S.length (format_header h pn_len npn) < pow2 20 - 17)
  = assert_norm(54 < pow2 20 - 17)

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


/// @irakoton rewrite code before, so that the code is not inlined
#push-options "--z3rlimit 20"
let encrypt a k siv hpk pn_len seqn plain =
  let open FStar.Endianness in
  assert_norm(8 `op_Multiply` 12 == 96);
  assert_norm(pow2 62 < pow2 96 /\ pow2 16 < pow2 62 /\ pow2 16 < pow2 20 - 17);
  let pnb = n_to_be 12 seqn in
  let npn : lbytes (1+pn_len) = S.slice pnb (11 - pn_len) 12 in
  let header = format_header plain pn_len npn in
  lemma_aead_maxlen a;
  lemma_format_len plain pn_len npn;
  let payload : AEAD.plain a =
    match plain with
    | Short _ _ _ p -> p
    | Long _ _ _ _ _ _ p -> p in
  let iv = xor_inplace pnb siv 0 in
  let cipher = AEAD.encrypt #a k iv header payload in
  let pn_offset =
    match plain with
    | Short _ _ cid _ -> 1 + S.length cid
    | Long _ _ dcil scil _ _ p -> 6 + add3 dcil + add3 scil + vlen (S.length p) in
  let sample = S.slice cipher (3-pn_len) (19-pn_len) in
  let mask = C16.block (calg_of_ae a) hpk sample in
  let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
  let sflags = if Short? plain then 0x1fuy else 0x0fuy in
  let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in
  let r = xor_inplace S.(header @| cipher) fmask 0 in
  let r = xor_inplace r pnmask pn_offset in
  assert_norm(54 + pow2 20 < pow2 32); r
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
let decrypt a k siv hpk last cid packet =
  let open FStar.Math.Lemmas in
  let open FStar.Endianness in
  let f = S.index packet 0 in
  let is_short = U8.(f <^ 128uy) in
  (* See https://tools.ietf.org/html/draft-ietf-quic-tls-19#section-5.4.2 *)
  let sample_offset : option (n:nat{n + 16 <= S.length packet}) =
    if is_short then
      let offset = 5 + S.length cid in
      (if offset + 16 <= S.length packet then Some offset else None)
    else
      let dcb = U8.v (S.index packet 5) in
      let dcil, scil = dcb / 0x10, dcb % 0x10 in
      let _ = modulo_range_lemma dcb 0x10 in
      let l_offset = 6 + add3 dcil + add3 scil in
      (if l_offset >= S.length packet then None else

      match parse_varint (S.slice packet l_offset (S.length packet)) with
      | None -> None
      | Some (l, vls) ->
        let offset = l_offset + vls + 4 in
        if offset + 16 <= S.length packet then Some offset else None)
    in
  match sample_offset with
  | None -> Failure
  | Some so ->
    let sample = S.slice packet so (so + 16) in
    let mask = C16.block (calg_of_ae a) hpk sample in
    let sflags = if is_short then 0x1fuy else 0x0fuy in
    let fmask = S.create 1 U8.(S.index mask 0 `logand` sflags) in    
    let packet' = xor_inplace packet fmask 0 in
    let flags = U8.v (S.index packet' 0) in
    let pn_len : nat2 = modulo_range_lemma flags 4; flags % 4 in
    let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
    let pn_offset = so - 3 + pn_len in
    let packet'' = xor_inplace packet' pnmask pn_offset in
    let npn = be_to_n (S.slice packet'' pn_offset (pn_offset + pn_len + 1)) in
    let pn = expand_npn last pn_len npn in
    let pnb = n_to_be 12 pn in
    let iv = xor_inplace pnb siv 0 in
    let aad = Seq.slice packet'' 0 (pn_offset + pn_len + 1) in
    let cipher = Seq.slice packet'' (pn_offset + pn_len + 1) (S.length packet'') in
    match AEAD.decrypt #a k pnb aad cipher with
    | None -> Failure
    | Some plain ->
      admit()
      //Success pn_len npn
#pop-options


