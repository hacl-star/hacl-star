module Lib.ByteSequence

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes
open Lib.LoopCombinators

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

/// BEGIN constant-time sequence equality

val lemma_not_equal_slice: #a:Type -> b1:Seq.seq a -> b2:Seq.seq a -> i:nat -> j:nat ->
  k:nat{i <= j /\ i <= k /\ j <= k /\ k <= Seq.length b1 /\ k <= Seq.length b2 } ->
  Lemma
    (requires ~(Seq.equal (Seq.slice b1 i j) (Seq.slice b2 i j)))
    (ensures  ~(Seq.equal (Seq.slice b1 i k) (Seq.slice b2 i k)))
let lemma_not_equal_slice #a b1 b2 i j k =
  assert (forall (n:nat{n < k - i}). Seq.index (Seq.slice b1 i k) n == Seq.index b1 (n + i))

val lemma_not_equal_last: #a:Type -> b1:Seq.seq a -> b2:Seq.seq a -> i:nat ->
  j:nat{i < j /\ j <= Seq.length b1 /\ j <= Seq.length b2} ->
  Lemma
    (requires ~(Seq.index b1 (j - 1) == Seq.index b2 (j - 1)))
    (ensures  ~(Seq.equal (Seq.slice b1 i j) (Seq.slice b2 i j)))
let lemma_not_equal_last #a b1 b2 i j =
  Seq.lemma_index_slice b1 i j (j - i - 1);
  Seq.lemma_index_slice b2 i j (j - i - 1)

val seq_eq_mask_inner: #t:inttype{~(S128? t)} -> #len1:size_nat -> #len2:size_nat
  -> b1:lseq (int_t t SEC) len1
  -> b2:lseq (int_t t SEC) len2
  -> len:size_nat{len <= len1 /\ len <= len2}
  -> i:size_nat{i < len}
  -> res:int_t t SEC{
      (sub b1 0 i == sub b2 0 i  ==> v res == v (ones t SEC)) /\
      (sub b1 0 i =!= sub b2 0 i ==> v res == v (zeros t SEC))}
  -> res':int_t t SEC{
      (sub b1 0 (i + 1) == sub b2 0 (i + 1)  ==> v res' == v (ones t SEC)) /\
      (sub b1 0 (i + 1) =!= sub b2 0 (i + 1) ==> v res' == v (zeros t SEC))}
let seq_eq_mask_inner #t #len1 #len2 b1 b2 len i res =
  logand_zeros (ones t SEC);
  logand_ones  (ones t SEC);
  logand_zeros (zeros t SEC);
  logand_ones  (zeros t SEC);
  let z0 = res in
  let res = eq_mask b1.[i] b2.[i] &. z0 in
  logand_spec (eq_mask b1.[i] b2.[i]) z0;
  if v res = ones_v t then
    begin
    let s1 = sub b1 0 (i + 1) in
    let s2 = sub b2 0 (i + 1) in
    Seq.lemma_split s1 i;
    Seq.lemma_split s2 i;
    assert (equal s1 s2)
    end
  else if v z0 = 0 then
    lemma_not_equal_slice b1 b2 0 i (i + 1)
  else
    lemma_not_equal_last b1 b2 0 (i + 1);
  res

let seq_eq_mask #t #len1 #len2 b1 b2 len =
  repeati_inductive len
    (fun (i:nat{i <= len}) res ->
      (sub b1 0 i == sub b2 0 i  ==> v res == v (ones t SEC)) /\
      (sub b1 0 i =!= sub b2 0 i ==> v res == v (zeros t SEC)))
    (seq_eq_mask_inner b1 b2 len)
    (ones t SEC)

let lbytes_eq #len b1 b2 =
  let res = seq_eq_mask b1 b2 len in
  RawIntTypes.u8_to_UInt8 res = 255uy

/// END constant-time sequence equality

val nat_from_intseq_be_:
    #t:inttype{unsigned t} -> #l:secrecy_level
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
    #t:inttype{unsigned t} -> #l:secrecy_level
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

#set-options "--max_fuel 1"

val nat_to_intseq_be_:
    #t:inttype{unsigned t} -> #l:secrecy_level
  -> len:nat
  -> n:nat{n < pow2 (bits t * len)}
  -> Tot (b:seq (int_t t l){length b == len /\ n == nat_from_intseq_be b}) (decreases len)
let rec nat_to_intseq_be_ #t #l len n =
  if len = 0 then create len (uint #t #l 0)
  else
    let len' = len - 1 in
    let tt = uint #t #l (n % modulus t) in
    let n' = n / modulus t in
    assert (modulus t = pow2 (bits t));
    FStar.Math.Lemmas.lemma_div_lt_nat n (bits t * len) (bits t);
    let b' = nat_to_intseq_be_ len' n' in
    let b  = Seq.append b' (create 1 tt) in
    Seq.append_slices b' (create 1 tt);
    b

let nat_to_intseq_be = nat_to_intseq_be_

val nat_to_intseq_le_:
    #t:inttype{unsigned t} -> #l:secrecy_level
  -> len:nat
  -> n:nat{n < pow2 (bits t * len)}
  -> Tot (b:seq (uint_t t l){length b == len /\ n == nat_from_intseq_le b}) (decreases len)
let rec nat_to_intseq_le_ #t #l len n =
  if len = 0 then create len (uint #t #l 0)
  else
    let len' = len - 1 in
    let tt = uint #t #l (n % modulus t) in
    let n' = n / modulus t in
    assert (modulus t = pow2 (bits t));
    FStar.Math.Lemmas.lemma_div_lt_nat n (bits t * len) (bits t);
    let b' = nat_to_intseq_le_ len' n' in
    let b = Seq.append (create 1 tt) b' in
    Seq.append_slices (create 1 tt) b';
    b

let nat_to_intseq_le = nat_to_intseq_le_
let nat_to_bytes_be = nat_to_intseq_be_ #U8
let nat_to_bytes_le = nat_to_intseq_le_ #U8

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 0"

val index_nat_to_intseq_le:
    #t:inttype{unsigned t}
  -> #l:secrecy_level
  -> len:size_nat
  -> n:nat{n < pow2 (bits t * len)}
  -> i:nat{i < len}
  -> Lemma (Seq.index (nat_to_intseq_le #t #l len n) i ==
           uint #t #l (n / pow2 (bits t * i) % pow2 (bits t)))
let rec index_nat_to_intseq_le #t #l len n i =
  if i = 0 then ()
  else
    begin
    calc (==) {
      Seq.index (nat_to_intseq_le #t #l (len - 1) (n / modulus t)) (i - 1);
      == { index_nat_to_intseq_le #t #l (len - 1) (n / modulus t) (i - 1) }
      uint ((n / modulus t) / pow2 (bits t * (i - 1)) % modulus t);
      == { Math.Lemmas.division_multiplication_lemma n (modulus t) (pow2 (bits t * (i - 1))) }
      uint ((n / (pow2 (bits t) * pow2 (bits t * (i - 1)))) % modulus t);
      == { Math.Lemmas.pow2_plus (bits t) (bits t * (i - 1)) }
      uint ((n / pow2 (bits t + bits t * (i - 1))) % modulus t);
      == { Math.Lemmas.distributivity_add_right (bits t) i (-1) }
      uint (n / pow2 (bits t + (bits t * i - bits t)) % modulus t);
      == { }
      uint (n / pow2 (bits t * i) % modulus t);
      == { }
      uint (n / pow2 (bits t * i) % (pow2 (bits t)));
    }
    end

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let uint_to_bytes_le #t #l n =
  nat_to_bytes_le (numbytes t) (uint_to_nat n)

let index_uint_to_bytes_le #t #l u =
  Classical.forall_intro (index_nat_to_intseq_le #U8 #l (numbytes t) (uint_to_nat u))

let uint_to_bytes_be #t #l n =
  nat_to_bytes_be (numbytes t) (uint_to_nat n)

let uint_from_bytes_le #t #l b =
  let n = nat_from_intseq_le #U8 b in
  uint #t #l n

let uint_from_bytes_be #t #l b =
  let n = nat_from_intseq_be #U8 b in
  uint #t #l n

val uints_to_bytes_le_inner: #t:inttype{unsigned t} -> #l:secrecy_level
  -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (int_t t l) len
  -> i:nat{i < len} -> unit -> unit & (lseq (uint_t U8 l) (numbytes t))
let uints_to_bytes_le_inner #t #l #len b i () =
  let open Lib.Sequence in
  (), uint_to_bytes_le #t #l b.[i]

let uints_to_bytes_le #t #l #len ul =
  let a_spec (i:nat{i <= len}) = unit in
  let _, o = generate_blocks (numbytes t) len len a_spec
    (uints_to_bytes_le_inner #t #l #len ul) () in
  o

(* Could also be written more simply as:
let uints_to_bytes_le #t #l #len ul =
  createi (len * numbytes t)
    (fun i -> let s = uint_to_bytes_le ul.[i / numbytes t] in
           s.[i % numbytes t])
*)

let index_uints_to_bytes_le #t #l #len ul i =
  index_generate_blocks (numbytes t) len len (uints_to_bytes_le_inner #t #l #len ul) i

val uints_to_bytes_be_inner: #t:inttype{unsigned t} -> #l:secrecy_level
  -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (int_t t l) len
  -> i:nat{i < len} -> unit -> unit & (lseq (uint_t U8 l) (numbytes t))
let uints_to_bytes_be_inner #t #l #len b i () =
  let open Lib.Sequence in
  (), uint_to_bytes_be #t #l b.[i]

let uints_to_bytes_be #t #l #len ul =
  let a_spec (i:nat{i <= len}) = unit in
  let _, o = generate_blocks (numbytes t) len len a_spec
    (uints_to_bytes_be_inner #t #l #len ul) () in
  o

let index_uints_to_bytes_be #t #l #len ul i =
  index_generate_blocks (numbytes t) len len (uints_to_bytes_be_inner #t #l #len ul) i

let uints_from_bytes_le #t #l #len b =
  Lib.Sequence.createi #(int_t t l) len
    (fun i -> uint_from_bytes_le (sub b (i * numbytes t) (numbytes t)))

let index_uints_from_bytes_le #t #l #len b i = ()

let uints_from_bytes_be #t #l #len b =
  Lib.Sequence.createi #(int_t t l) len
    (fun i -> uint_from_bytes_be (sub b (i * numbytes t) (numbytes t)))

let index_uints_from_bytes_be #t #l #len b i = ()

let uint_at_index_le #t #l #len b i =
  uint_from_bytes_le (sub b (i * numbytes t) (numbytes t))

let uint_at_index_be #t #l #len b i =
  uint_from_bytes_be (sub b (i * numbytes t) (numbytes t))

#push-options "--max_fuel 1"

val nat_from_intseq_slice_lemma_aux: len:pos -> a:nat -> b:nat -> c:nat -> i:pos{i <= len} ->
  Lemma (pow2 ((i - 1) * c) * (a + pow2 c * b) == pow2 ((i - 1) * c) * a + pow2 (i * c) * b)
let nat_from_intseq_slice_lemma_aux len a b c i =
  FStar.Math.Lemmas.distributivity_add_right (pow2 ((i - 1) * c)) a (pow2 c * b);
  FStar.Math.Lemmas.paren_mul_right (pow2 ((i - 1) * c)) (pow2 c) b;
  FStar.Math.Lemmas.pow2_plus ((i - 1) * c) c

val nat_from_intseq_le_slice_lemma_:
    #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat
  -> b:lseq (int_t t l) len
  -> i:nat{i <= len} ->
  Lemma (nat_from_intseq_le_ b == nat_from_intseq_le_ (slice b 0 i) + pow2 (i * bits t) * nat_from_intseq_le_ (slice b i len))
let rec nat_from_intseq_le_slice_lemma_ #t #l #len b i =
  if len = 0 then ()
  else begin
    if i = 0 then ()
    else begin
      let b1 = slice b 0 i in
      nat_from_intseq_le_slice_lemma_ #t #l #i b1 (i - 1);
      assert (nat_from_intseq_le_ b1 == nat_from_intseq_le_ (slice b 0 (i - 1)) + pow2 ((i - 1) * bits t) * v b.[i - 1]);
      nat_from_intseq_le_slice_lemma_ #t #l #len b (i - 1);
      assert (nat_from_intseq_le_ b == nat_from_intseq_le_ (slice b 0 (i - 1)) + pow2 ((i - 1) * bits t) * nat_from_intseq_le_ (slice b (i - 1) len));
      nat_from_intseq_slice_lemma_aux len (v b.[i - 1]) (nat_from_intseq_le_ (slice b i len)) (bits t) i
    end
  end

let nat_from_intseq_le_lemma0 #t #l b = ()

let nat_from_intseq_le_slice_lemma #t #l #len b i =
  nat_from_intseq_le_slice_lemma_ b i

val nat_from_intseq_be_slice_lemma_:
    #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat
  -> b:lseq (int_t t l) len
  -> i:nat{i <= len} ->
  Lemma (ensures (nat_from_intseq_be_ b == nat_from_intseq_be_ (slice b i len) + pow2 ((len - i) * bits t) * nat_from_intseq_be_ (slice b 0 i)))
  (decreases (len - i))
let rec nat_from_intseq_be_slice_lemma_ #t #l #len b i =
  if len = 0 then ()
  else begin
    if i = len then ()
    else begin
      let b1 = slice b i len in
      nat_from_intseq_be_slice_lemma_ #t #l #(len - i) b1 1;
      assert (nat_from_intseq_be_ b1 == nat_from_intseq_be_ (slice b (i + 1) len) + pow2 ((len - i - 1) * bits t) * v b.[i]);
      nat_from_intseq_be_slice_lemma_ #t #l #len b (i + 1);
      assert (nat_from_intseq_be_ b == nat_from_intseq_be_ (slice b (i + 1) len) + pow2 ((len - i - 1) * bits t) * nat_from_intseq_be_ (slice b 0 (i + 1)));
      nat_from_intseq_slice_lemma_aux len (v b.[i]) (nat_from_intseq_be_ (slice b 0 i)) (bits t) (len - i)
    end
  end

let nat_from_intseq_be_lemma0 #t #l b = ()
#pop-options

let nat_from_intseq_be_slice_lemma #t #l #len b i =
  nat_from_intseq_be_slice_lemma_ #t #l #len b i

val uints_from_bytes_le_slice_lemma_lp:
    #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_pos{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) -> i:nat -> j:nat{i <= j /\ j <= len} -> k:nat{k < j - i} ->
  Lemma (index (slice (uints_from_bytes_le #t #l #len b) i j) k ==
         uint_from_bytes_le (sub b ((i + k) * numbytes t) (numbytes t)))
let uints_from_bytes_le_slice_lemma_lp #t #l #len b i j k =
  let r = slice (uints_from_bytes_le #t #l #len b) i j in
  index_uints_from_bytes_le #t #l #len b (i + k);
  assert (r.[k] == uint_from_bytes_le (sub b ((i + k) * numbytes t) (numbytes t)))

val uints_from_bytes_le_slice_lemma_rp:
    #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_pos{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) -> i:nat -> j:nat{i <= j /\ j <= len} -> k:nat{k < j - i} ->
  Lemma (index (uints_from_bytes_le #t #l #(j-i) (slice b (i * numbytes t) (j * numbytes t))) k ==
         uint_from_bytes_le (sub b ((i + k) * numbytes t) (numbytes t)))
let uints_from_bytes_le_slice_lemma_rp #t #l #len b i j k =
  let b1 = slice b (i * numbytes t) (j * numbytes t) in
  let r = uints_from_bytes_le #t #l #(j-i) b1 in
  index_uints_from_bytes_le #t #l #(j-i) b1 k;
  assert (r.[k] == uint_from_bytes_le (sub b1 (k * numbytes t) (numbytes t)));
  assert (r.[k] == uint_from_bytes_le (sub b ((i + k) * numbytes t) (numbytes t)))

let uints_from_bytes_le_slice_lemma #t #l #len b i j =
  FStar.Classical.forall_intro (uints_from_bytes_le_slice_lemma_lp #t #l #len b i j);
  FStar.Classical.forall_intro (uints_from_bytes_le_slice_lemma_rp #t #l #len b i j);
  eq_intro (slice (uints_from_bytes_le #t #l #len b) i j) (uints_from_bytes_le #t #l #(j-i) (slice b (i * numbytes t) (j * numbytes t)))

#push-options "--max_fuel 1"
val uints_from_bytes_le_nat_lemma_aux:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> #len:size_pos{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (nat_from_intseq_le_ (uints_from_bytes_le #t #l #len b) ==
         nat_from_intseq_le_ (slice b 0 (numbytes t)) + pow2 (bits t) *
         nat_from_intseq_le_ (uints_from_bytes_le #t #l #(len-1) (slice b (numbytes t) (len * numbytes t))))
let uints_from_bytes_le_nat_lemma_aux #t #l #len b =
  let r = uints_from_bytes_le #t #l #len b in
  assert (nat_from_intseq_le_ r == v r.[0] + pow2 (bits t) * nat_from_intseq_le_ (slice r 1 len));
  assert (nat_from_intseq_le_ (slice b 0 (numbytes t)) == v r.[0]);
  uints_from_bytes_le_slice_lemma #t #l #len b 1 len;
  assert (slice r 1 len == uints_from_bytes_le #t #l #(len-1) (slice b (numbytes t) (len * numbytes t)))

val uints_from_bytes_le_nat_lemma_:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (nat_from_intseq_le_ (uints_from_bytes_le #t #l #len b) == nat_from_intseq_le_ b)
let rec uints_from_bytes_le_nat_lemma_ #t #l #len b =
  if len = 0 then ()
  else begin
    let b1 = slice b (numbytes t) (len * numbytes t) in
    nat_from_intseq_le_slice_lemma_ #U8 #l #(len * numbytes t) b (numbytes t);
    assert (nat_from_intseq_le_ b == nat_from_intseq_le_ (slice b 0 (numbytes t)) + pow2 (bits t) * nat_from_intseq_le_ b1);
    uints_from_bytes_le_nat_lemma_ #t #l #(len - 1) b1;
    assert (nat_from_intseq_le_ (uints_from_bytes_le #t #l #(len - 1) b1) == nat_from_intseq_le_ b1);
    uints_from_bytes_le_nat_lemma_aux #t #l #len b
  end
#pop-options

let uints_from_bytes_le_nat_lemma #t #l #len b =
  uints_from_bytes_le_nat_lemma_ #t #l #len b

val index_uints_to_bytes_le_aux:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> len:nat{len * numbytes t < pow2 32}
  -> n:nat{n < pow2 (bits t * len)}
  -> i:nat{i < len * numbytes t}
  -> Lemma (let s:lseq (int_t t l) len = nat_to_intseq_le #t #l len n in
           Seq.index (uints_to_bytes_le #t #l #len s) i ==
           Seq.index (nat_to_bytes_le #l (numbytes t) (uint_to_nat s.[i / numbytes t])) (i % numbytes t))
let index_uints_to_bytes_le_aux #t #l len n i =
  let open Lib.Sequence in
  let s: lseq (int_t t l) len = nat_to_intseq_le #t #l len n in
  index_generate_blocks (numbytes t) len len
    (uints_to_bytes_le_inner #t #l #len s) i

private
val modulo_pow2_prop: r:pos -> a:nat -> b:nat -> c:nat{c < b} -> Lemma
  ((a % pow2 (r * b) / pow2 (r * c)) % pow2 r == (a / pow2 (r * c)) % pow2 r)
let modulo_pow2_prop r a b c =
  calc (==) {
    ((a % pow2 (r * b)) / pow2 (r * c)) % pow2 r;
    == { Math.Lemmas.pow2_modulo_division_lemma_1 a (r * c) (r * b) }
    ((a / pow2 (r * c) % pow2 (r * b - r * c))) % pow2 r;
    == { Math.Lemmas.lemma_mul_sub_distr r b c }
    ((a / pow2 (r * c) % pow2 (r * (b - c)))) % pow2 r;
    == { Math.Lemmas.pow2_plus r (r * (b - c) - r) }
    (a / pow2 (r * c)) % (pow2 r * pow2 (r * (b - c) - r)) % pow2 r;
    == { Math.Lemmas.modulo_modulo_lemma (a / pow2 (r * c)) (pow2 r) (pow2 (r * (b - c) - r))}
    (a / pow2 (r * c)) % pow2 r;
  }

val index_nat_to_intseq_to_bytes_le_aux: m:pos -> i:nat ->
  Lemma ((8 * m) * (i / m) == 8 * (i - i % m))
let index_nat_to_intseq_to_bytes_le_aux m i =
  FStar.Math.Lemmas.paren_mul_right 8 m (i / m);
  FStar.Math.Lemmas.euclidean_division_definition i m

val index_nat_to_intseq_to_bytes_le:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> len:nat{len * numbytes t < pow2 32}
  -> n:nat{n < pow2 (bits t * len)}
  -> i:nat{i < len * numbytes t}
  -> Lemma (let s:lseq (int_t t l) len = nat_to_intseq_le #t #l len n in
           Seq.index (nat_to_bytes_le #l (numbytes t) (uint_to_nat s.[i / numbytes t])) (i % numbytes t) ==
           Seq.index (nat_to_bytes_le #l (len * numbytes t) n) i)
let index_nat_to_intseq_to_bytes_le #t #l len n i =
  let s:lseq (int_t t l) len = nat_to_intseq_le #t #l len n in
  let m = numbytes t in
  index_nat_to_intseq_le #U8 #l (len * m) n i;
  assert (Seq.index (nat_to_bytes_le #l (len * m) n) i ==
          uint (n / pow2 (8 * i) % pow2 8));
  index_nat_to_intseq_le #U8 #l m (uint_to_nat s.[i / m]) (i % m);
  assert (Seq.index (nat_to_bytes_le #l m
    (uint_to_nat s.[i / m])) (i % m) ==
     uint (uint_to_nat s.[i / m] / pow2 (8 * (i % m)) % pow2 8));
  index_nat_to_intseq_le #t #l len n (i / m);
  assert (bits t == 8 * m);
  assert (s.[i / m] == uint (n / pow2 (bits t * (i / m)) % pow2 (bits t)));
  modulo_pow2_prop 8 (n / pow2 (8 * i - 8 * (i % m))) m (i % m);
  calc (==) {
    n / pow2 (bits t * (i / m)) % pow2 (bits t) / pow2 (8 * (i % m)) % pow2 8;
    == { assert (bits t == 8 * m) }
    n / pow2 ((8 * m) * (i / m)) % pow2 (8 * m) / pow2 (8 * (i % m)) % pow2 8;
    == { index_nat_to_intseq_to_bytes_le_aux m i }
    n / pow2 (8 * (i - i % m)) % pow2 (8 * m) / pow2 (8 * (i % m)) % pow2 8;
    == { Math.Lemmas.distributivity_sub_right 8 i (i % m) }
    n / pow2 (8 * i - 8 * (i % m)) % pow2 (8 * m) / pow2 (8 * (i % m)) % pow2 8;
    == { modulo_pow2_prop 8 (n / pow2 (8 * i - 8 * (i % m))) m (i % m) }
    (n / pow2 (8 * i - 8 * (i % m))) / pow2 (8 * (i % m)) % pow2 8;
    == { Math.Lemmas.division_multiplication_lemma n
          (pow2 (8 * i - 8 * (i % m))) (pow2 (8 * (i % m))) }
    (n / (pow2 (8 * i - 8 * (i % m)) * pow2 (8 * (i % m)))) % pow2 8;
    == { Math.Lemmas.pow2_plus (8 * i - 8 * (i % m)) (8 * (i % m)) }
    (n / pow2 (8 * i)) % pow2 8;
  }

let uints_to_bytes_le_nat_lemma #t #l len n =
  Classical.forall_intro (index_uints_to_bytes_le_aux #t #l len n);
  Classical.forall_intro (index_nat_to_intseq_to_bytes_le #t #l len n);
  Seq.lemma_eq_intro
    (uints_to_bytes_le #t #l #len (nat_to_intseq_le #t #l len n))
    (nat_to_bytes_le (len * numbytes t) n)

#push-options "--max_fuel 1"

let rec nat_from_intseq_le_inj #t #l b1 b2 =
  if length b1 = 0 then ()
  else begin
    nat_from_intseq_le_inj (Seq.slice b1 1 (length b1)) (Seq.slice b2 1 (length b2));
    Seq.lemma_split b1 1;
    Seq.lemma_split b2 1
  end

let rec nat_from_intseq_be_inj #t #l b1 b2 =
  if length b1 = 0 then ()
  else begin
    nat_from_intseq_be_inj (Seq.slice b1 0 (length b1 - 1)) (Seq.slice b2 0 (length b2 - 1));
    Seq.lemma_split b1 (length b1 - 1);
    Seq.lemma_split b2 (length b2 - 1)
  end

let lemma_nat_to_from_bytes_be_preserves_value #l b len x = ()

let lemma_nat_to_from_bytes_le_preserves_value #l b len x = ()

let lemma_uint_to_bytes_le_preserves_value #t #l x = ()

let lemma_uint_to_bytes_be_preserves_value #t #l x = ()

let lemma_nat_from_to_intseq_le_preserves_value #t #l len b =
  nat_from_intseq_le_inj (nat_to_intseq_le len (nat_from_intseq_le b)) b

let lemma_nat_from_to_bytes_le_preserves_value #l b len =
  lemma_nat_from_to_intseq_le_preserves_value len b

let lemma_reveal_uint_to_bytes_le #t #l b = ()

let lemma_reveal_uint_to_bytes_be #t #l b = ()
