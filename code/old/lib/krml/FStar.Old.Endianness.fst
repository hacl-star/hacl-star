module FStar.Old.Endianness

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.UInt32
open FStar.Ghost
open FStar.Mul
open FStar.Int.Cast.Full

module U8 = FStar.UInt8

let u8  = UInt8.t
let u32 = UInt32.t
let u64 = UInt64.t

#set-options "--initial_fuel 0 --max_fuel 0"

type bytes  = Seq.seq U8.t // Pure sequence of bytes

type  lbytes  (l:nat) = b:bytes   {Seq.length b == l}

(* type lbuffer (l:nat) = b:buffer {Buffer.length b == l} *)

#reset-options

let uint128_to_uint8 (a:UInt128.t) : Tot (b:UInt8.t{UInt8.v b = UInt128.v a % pow2 8})
  = Math.Lemmas.pow2_modulo_modulo_lemma_2 (UInt128.v a) 64 8;
    uint64_to_uint8 (uint128_to_uint64 a)

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"


open FStar.Seq

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:bytes) : Tot (n:nat) (decreases (Seq.length b)) =
  if Seq.length b = 0 then 0
  else
    UInt8.v (head b) + pow2 8 * little_endian (tail b)

(* Big endian integer value of a sequence of bytes *)
let rec big_endian (b:bytes) : Tot (n:nat) (decreases (Seq.length b)) = 
  if Seq.length b = 0 then 0 
  else
    UInt8.v (last b) + pow2 8 * big_endian (Seq.slice b 0 (Seq.length b - 1))

#reset-options "--initial_fuel 1 --max_fuel 1"

val little_endian_null: len:nat{len < 16} -> Lemma
  (little_endian (Seq.create len 0uy) == 0)
let rec little_endian_null len =
  if len = 0 then ()
  else
    begin
    Seq.lemma_eq_intro (Seq.slice (Seq.create len 0uy) 1 len)
		       (Seq.create (len - 1) 0uy);
    assert (little_endian (Seq.create len 0uy) ==
      0 + pow2 8 * little_endian (Seq.slice (Seq.create len 0uy) 1 len));
    little_endian_null (len - 1)
    end

val little_endian_singleton: n:UInt8.t -> Lemma
  (little_endian (Seq.create 1 n) == UInt8.v n)
let little_endian_singleton n =
  assert (little_endian (Seq.create 1 n) ==
    UInt8.v (Seq.index (Seq.create 1 n) 0) + pow2 8 *
    little_endian (Seq.slice (Seq.create 1 n) 1 1))


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

val little_endian_append: w1:bytes -> w2:bytes -> Lemma
  (requires True)
  (ensures
    little_endian (Seq.append w1 w2) ==
    little_endian w1 + pow2 (8 * Seq.length w1) * little_endian w2)
  (decreases (Seq.length w1))
let rec little_endian_append w1 w2 =
  let open FStar.Seq in
  if length w1 = 0 then
    begin
    assert_norm (pow2 (8 * 0) == 1);
    Seq.lemma_eq_intro (append w1 w2) w2
    end
  else
    begin
    let w1' = slice w1 1 (length w1) in
    assert (length w1' == length w1 - 1);
    little_endian_append w1' w2;
    assert (index (append w1 w2) 0 == index w1 0);
    Seq.lemma_eq_intro
      (append w1' w2)
      (Seq.slice (append w1 w2) 1 (length (append w1 w2)));
    assert (little_endian (append w1 w2) ==
      UInt8.v (index w1 0) + pow2 8 * little_endian (append w1' w2));
    assert (little_endian (append w1' w2) ==
      little_endian w1' + pow2 (8 * length w1') * little_endian w2);
    assert (UInt8.v (index w1 0) + pow2 8 * little_endian (append w1' w2) ==
      UInt8.v (index w1 0) +
      pow2 8 * (little_endian w1' + pow2 (8 * length w1') * little_endian w2));
    Math.Lemmas.pow2_plus 8 (8 * (length w1 - 1));
    assert (pow2 8 * pow2 (8 * length w1') == pow2 (8 * length w1));
    assert (UInt8.v (index w1 0) + pow2 8 * little_endian (append w1' w2) ==
      UInt8.v (index w1 0) +
      pow2 8 * little_endian w1' + pow2 (8 * length w1) * little_endian w2);
    assert (UInt8.v (index w1 0) + pow2 8 * little_endian w1' == little_endian w1)
    end


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

val lemma_euclidean_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidean_division r b q = ()

private val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b == a * (b + 1))
let lemma_factorise a b = ()

val lemma_little_endian_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (little_endian b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))
let rec lemma_little_endian_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 1 (Seq.length b) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_little_endian_is_bounded s;
    assert(UInt8.v (Seq.index b 0) < pow2 8);
    assert(little_endian s < pow2 (8 * Seq.length s));
    assert(little_endian b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (UInt8.v (Seq.index b 0)) (little_endian s) (pow2 8);
    assert(little_endian b <= pow2 8 * (little_endian s + 1));
    assert(little_endian b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end

val lemma_big_endian_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (big_endian b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))
  [SMTPat (big_endian b)]
let rec lemma_big_endian_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 0 (Seq.length b - 1) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_big_endian_is_bounded s;
    assert(UInt8.v (Seq.last b) < pow2 8);
    assert(big_endian s < pow2 (8 * Seq.length s));
    assert(big_endian b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (UInt8.v (Seq.last b)) (big_endian s) (pow2 8);
    assert(big_endian b <= pow2 8 * (big_endian s + 1));
    assert(big_endian b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end


#reset-options "--initial_fuel 0 --max_fuel 0"

val lemma_little_endian_lt_2_128: b:bytes {Seq.length b <= 16} -> Lemma
  (requires True)
  (ensures  (little_endian b < pow2 128))
  [SMTPat (little_endian b)]
let lemma_little_endian_lt_2_128 b =
  lemma_little_endian_is_bounded b;
  if Seq.length b = 16 then ()
  else Math.Lemmas.pow2_lt_compat 128 (8 * Seq.length b)


#reset-options "--z3rlimit 100 --max_fuel 1 --initial_fuel 1"

val uint8_to_uint128: a:UInt8.t -> Tot (b:UInt128.t{UInt128.v b == UInt8.v a})
let uint8_to_uint128 a = uint64_to_uint128 (uint8_to_uint64 a)


// turns an integer into a bytestream, little-endian
val little_bytes: 
  len:UInt32.t -> n:nat{n < pow2 (8 * v len)} ->
  Tot (b:lbytes (v len) {n == little_endian b}) (decreases (v len))
let rec little_bytes len n = 
  if len = 0ul then 
    Seq.empty 
  else
    let len = len -^ 1ul in 
    let byte = UInt8.uint_to_t (n % 256) in
    let n' = n / 256 in 
    Math.Lemmas.pow2_plus 8 (8 * v len);
    assert(n' < pow2 (8 * v len ));
    let b' = little_bytes len n' in
    let b = cons byte b' in
    assert(Seq.equal b' (tail b));
    b

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"


(* injectivity proofs for byte encodings *) 

type word = b:Seq.seq UInt8.t {Seq.length b <= 16}
open FStar.Math.Lib
open FStar.Math.Lemmas

private let endian_is_injective q r q' r' : Lemma
  (requires UInt8.v r + pow2 8 * q = UInt8.v r' + pow2 8 * q')
  (ensures r = r' /\ q = q') =
  lemma_mod_injective (pow2 8) (UInt8.v r) (UInt8.v r')

private let big_endian_step (b:word{length b > 0}) : 
  Lemma (big_endian b = U8.v (last b) + pow2 8 * big_endian (slice b 0 (length b - 1))) =
  ()

#reset-options "--z3rlimit 100"
val lemma_big_endian_inj: b:word -> b':word {length b = length b'} -> Lemma
  (requires big_endian b = big_endian b')
  (ensures b == b')
  (decreases (length b))
let rec lemma_big_endian_inj s s' = 
  let len = length s in 
  if len = 0 then lemma_eq_intro s s'
  else
    let t = slice s 0 (len - 1) in 
    let x = last s in 
    lemma_eq_intro s (snoc t x);
    big_endian_step s;
    let t' = slice s' 0 (len - 1) in 
    let x' = last s' in 
    lemma_eq_intro s' (snoc t' x');
    big_endian_step s';
    endian_is_injective (big_endian t) x (big_endian t') x';
    lemma_big_endian_inj t t'

(* the little endian proof could be simplified, as above *)

(* this lemma is used only Crypto.Symmetric.Poly1305 *)
val lemma_little_endian_is_injective_1: b:pos -> q:nat -> r:nat -> q':nat -> r':nat -> Lemma
  (requires (r < b /\ r' < b /\ r + b * q = r' + b * q'))
  (ensures  (r = r' /\ q = q'))
let lemma_little_endian_is_injective_1 b q r q' r' =
  lemma_mod_plus r q b;
  lemma_mod_plus r' q' b;
  lemma_mod_injective b r r'

(* a sequence associativity property: ... @ ([x] @ s) == ... @ [x]) @ s *)
private val lemma_little_endian_is_injective_2: b:bytes -> len:pos{len <= length b} -> Lemma
  (let s = slice b (length b - len) (length b) in 
   let s' = slice s 1 (length s) in
   let s'' = slice b (length b - (len - 1)) (length b) in
   s'' == s')
let lemma_little_endian_is_injective_2 b len =
  let s = slice b (length b - len) (length b) in
  let s' = slice s 1 (length s) in
  let s'' = slice b (length b - (len - 1)) (length b) in
  lemma_eq_intro s' s''

(* a sequence injectivity property *)
private val lemma_little_endian_is_injective_3: b:bytes -> b':bytes -> len:pos{len <= length b /\ len <= length b'} -> Lemma
  (requires 
    slice b (length b - (len - 1)) (length b) == slice b' (length b' - (len-1)) (length b') /\ 
    Seq.index b (length b - len) = Seq.index b' (length b' - len))
  (ensures slice b (length b - len) (length b) == slice b' (length b' - len) (length b'))
let lemma_little_endian_is_injective_3 b b' len =
  lemma_eq_intro (slice b (length b - len) (length b)) (cons (index b (length b - len)) (slice b (length b - (len-1)) (length b)));
  lemma_eq_intro (slice b' (length b' - len) (length b')) (cons (index b' (length b' - len)) (slice b' (length b' - (len-1)) (length b')))

private let little_endian_step (b:bytes{length b > 0}): 
  Lemma (little_endian b = U8.v (head b) + pow2 8 * little_endian (tail b)) 
  = ()

val lemma_little_endian_is_injective: b:bytes -> b':bytes -> len:nat{len <= length b /\ len <= length b'} -> Lemma
  (requires little_endian (slice b (length b - len) (length b)) = little_endian (slice b' (length b' - len) (length b')) )
  (ensures slice b (length b - len) (length b) == slice b' (length b' - len) (length b'))
let rec lemma_little_endian_is_injective b b' len =
  if len = 0 then
    lemma_eq_intro (slice b (length b - len) (length b)) (slice b' (length b' - len) (length b'))
  else
    let s = slice b (length b - len) (length b) in
    let s' = slice b' (length b' - len) (length b') in
    little_endian_step s; 
    little_endian_step s';
    endian_is_injective (little_endian (tail s)) (head s) (little_endian (tail s')) (head s');
    lemma_little_endian_is_injective_2 b len;
    lemma_little_endian_is_injective_2 b' len;
    lemma_little_endian_is_injective b b' (len - 1);
    lemma_little_endian_is_injective_3 b b' len

val lemma_little_endian_inj: b:bytes -> b':bytes {length b = length b'} -> Lemma
  (requires little_endian b = little_endian b')
  (ensures b == b')
let lemma_little_endian_inj b b' =
  let len = length b in 
  Seq.lemma_eq_intro b (Seq.slice b 0  len);
  Seq.lemma_eq_intro b' (Seq.slice b' 0  len);
  lemma_little_endian_is_injective b b' len


val uint32_bytes: 
  len:UInt32.t {v len <= 4} -> n:UInt32.t {UInt32.v n < pow2 (8 * v len)} -> 
  Tot (b:lbytes (v len) { UInt32.v n == little_endian b}) (decreases (v len))
let rec uint32_bytes len n = 
  if len = 0ul then 
    let e = Seq.empty #UInt8.t in
    assert_norm(0 = little_endian e);
    e
  else
    let len = len -^ 1ul in 
    let byte = uint32_to_uint8 n in
    let n1 = n in (* n defined in FStar.UInt32, so was shadowed, so renamed into n1 *)
    let n' = FStar.UInt32.(n1 >>^ 8ul) in 
    assert(v n = UInt8.v byte + 256 * v n');
    Math.Lemmas.pow2_plus 8 (8 * v len);
    assert_norm (pow2 8 == 256);
    assert(v n' < pow2 (8 * v len ));
    let b' = uint32_bytes len n'
    in 
    Seq.cons byte b'

val uint32_be: 
  len:UInt32.t {v len <= 4} -> n:UInt32.t {UInt32.v n < pow2 (8 * v len)} -> 
  Tot (b:lbytes (v len) { UInt32.v n == big_endian b}) (decreases (v len))
let rec uint32_be len n = 
  if len = 0ul then 
    let e = Seq.empty #UInt8.t in
    assert_norm(0 = big_endian e);
    e
  else
    let len = len -^ 1ul in 
    let byte = uint32_to_uint8 n in
    let n1 = n in (* n shadowed by FStar.UInt32.n *)
    let n' = FStar.UInt32.(n1 >>^ 8ul) in 
    assert(v n = UInt8.v byte + 256 * v n');
    Math.Lemmas.pow2_plus 8 (8 * v len);
    assert_norm (pow2 8 == 256);
    assert(v n' < pow2 (8 * v len ));
    let b' = uint32_be len n'
    in 
    Seq.snoc b' byte 

#reset-options "--z3rlimit 400"

// turns an integer into a bytestream, big-endian
val big_bytes: 
  len:UInt32.t -> n:nat{n < pow2 (8 * v len)} ->
  Tot (b:lbytes (v len) {n == big_endian b}) (decreases (v len))
let rec big_bytes len n = 
  if len = 0ul then 
    Seq.empty 
  else
    let len = len -^ 1ul in 
    let byte = UInt8.uint_to_t (n % 256) in
    let n' = n / 256 in 
    Math.Lemmas.pow2_plus 8 (8 * v len);
    assert(n' < pow2 (8 * v len ));
    let b' = big_bytes len n' in
    let b'' = Seq.create 1 byte in
    let b = Seq.append b' b'' in
    assert(Seq.equal b' (Seq.slice b 0 (v len)));
    b
