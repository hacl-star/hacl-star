
//17-02-11 Using a variant of this file to experiment with full correctness verification.
//17-02-12 I'd like to keep as a simple reference implementation.
module Crypto.Symmetric.Chacha20

// Concrete implementation of CHACHA20 and countermode encryption
// Not much point verifying its against a more complex pure specification.

open FStar.Mul
open FStar.Ghost
(*  Machine integers *)
open FStar.UInt8
open FStar.UInt32
//open FStar.Int.Cast
(*  Effects and memory layout *)
open FStar.HyperStack
(*  Buffers *)
open FStar.Buffer
open Buffer.Utils

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module Spec = Hacl.Spec.Chacha20

(*** Chacha 20 ***)

type bytes = buffer UInt8.t

type lbytes l = b:bytes {length b = l}
type key   = lbytes Spec.keylen
type block = lbytes Spec.blocklen
type iv    = lbytes Spec.ivlen
type idx = n:UInt32.t {v n  < Spec.blocklen / 4}

// internally, blocks are represented as 16 x 4-byte integers
private type matrix = m:buffer UInt32.t {length m = Spec.blocklen / 4}

private type shuffle (spec: Spec.shuffle) = 
  m:matrix -> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> 
    live h0 m /\ live h1 m /\ modifies_1 m h0 h1 /\ 
    as_seq h1 m = spec (as_seq h0 m)))

//#reset-options "--z3rlimit 40"
(* lifted by hand for now: *)
private val line:
  m:matrix -> 
  a:idx -> 
  b:idx -> 
  d:idx -> 
  s:UInt32.t{v s < 32}-> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> 
    live h0 m /\ live h1 m /\ modifies_1 m h0 h1 /\ 
    as_seq h1 m = Spec.line (v a) (v b) (v d) s (as_seq h0 m)))
let line m a b d s = 
  m.(a) <- m.(a) +%^ m.(b);
  m.(d) <- Spec.rotate (m.(d) ^^  m.(a)) s

private val quarter_round:
  m:matrix -> 
  a:idx -> 
  b:idx -> 
  c:idx -> 
  d:idx -> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> 
    live h0 m /\ live h1 m /\ modifies_1 m h0 h1 /\
    as_seq h1 m = Spec.quarter_round (v a) (v b) (v c) (v d) (as_seq h0 m)
    ))
let quarter_round m a b c d = 
(*
  let line a b d s = 
    upd m a (m.(a) +%^ m.(b));
    upd m d((m.(d) ^^  m.(a)) <<< s) in
*)    
  line m a b d 16ul;
  line m c d b 12ul;
  line m a b d  8ul; 
  line m c d b  7ul

(*
  let open FStar.Buffer in
  m.(a) := m.(a) +%^ m.(b);
  m.(d) := (m.(d) ^^  m.(a)) <<< 16ul;
  m.(c) := m.(c) +%^ m.(d);
  m.(b) := (m.(b) ^^  m.(c)) <<< 12ul;
  m.(a) := m.(a) +%^ m.(b);
  m.(d) := (m.(d) ^^  m.(a)) <<< 8ul;
  m.(c) := m.(c) +%^ m.(d);
  m.(b) := (m.(b) ^^  m.(c)) <<< 7ul
*)

private val column_round: shuffle (Spec.column_round)
let column_round m =
  quarter_round m 0ul 4ul  8ul 12ul;
  quarter_round m 1ul 5ul  9ul 13ul;
  quarter_round m 2ul 6ul 10ul 14ul;
  quarter_round m 3ul 7ul 11ul 15ul

private val diagonal_round: shuffle (Spec.diagonal_round)
let diagonal_round m =
  quarter_round m 0ul 5ul 10ul 15ul;
  quarter_round m 1ul 6ul 11ul 12ul;
  quarter_round m 2ul 7ul  8ul 13ul;
  quarter_round m 3ul 4ul  9ul 14ul

private val double_round: shuffle (Spec.double_round) 
let double_round m = 
  column_round m; 
  diagonal_round m

val iter: n:UInt32.t -> spec: Spec.shuffle -> body: shuffle spec ->
  m:matrix -> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> 
    live h0 m /\ live h1 m /\ modifies_1 m h0 h1 /\ 
    as_seq h1 m = Spec.iter (v n) spec (as_seq h0 m)))
let rec iter n spec body m = 
  if n <> 0ul then (
    body m; 
    iter (n -^ 1ul) spec body m)
//17-02-12 I had to inline the more compact "shuffle (Spec.iter (v n) spec)";
//17-02-12 otherwise missing inferred decreases clause? this yields the same function:
// val iter': n:UInt32.t -> spec: Spec.shuffle -> body: shuffle spec -> shuffle (Spec.iter (v n) spec)
// let iter' = iter

private val rounds: shuffle (Spec.rounds)
let rounds m = (* 20 rounds *)
  iter 10ul Spec.double_round double_round m

private val chacha20_init: 
  m:matrix -> k:key{disjoint m k} -> n:iv{disjoint m n} -> counter:UInt32.t -> 
  STL unit
  (requires (fun h -> live h m /\ live h k /\ live h n ))
  (ensures (fun h0 _ h1 -> 
    live h0 m /\ live h0 k /\ live h0 n /\ 
    live h1 m /\ modifies_1 m h0 h1 /\ 
    as_seq h1 m = Spec.init0 (as_seq h0 k) (as_seq h0 n) counter (as_seq h0 m)
    ))

private val fill: m:matrix -> i:UInt32.t -> len:UInt32.t {v i + v len <= 16}-> src:bytes {length src = 4 * v len} -> 
  STL unit
  (requires (fun h -> live h m /\ live h src /\ disjoint m src))
  (ensures (fun h0 _ h1 -> 
    live h0 src /\ live h0 m /\ live h1 m /\ modifies_1 m h0 h1 /\
    as_seq h1 m = Spec.fill (v i) (v len) (as_seq h0 src) (as_seq h0 m)
    ))

#reset-options "--z3rlimit 30"

let rec fill m i len src =
  if len <> 0ul then (
    m.(i) <- uint32_of_bytes (sub src 0ul 4ul); 
    let len = len -^ 1ul in 
    fill m (i +^ 1ul) len (sub src 4ul (4ul *^ len));
    assume false //17-02-08 inductive functional corectness proof TBC
    )

//review handling of endianness

// RFC 7539 2.3
let chacha20_init m key iv counter =
  m.(0ul) <- Spec.constant_0;
  m.(1ul) <- Spec.constant_1;
  m.(2ul) <- Spec.constant_2;
  m.(3ul) <- Spec.constant_3;
  fill m 4ul 8ul key;
  m.(12ul) <- counter;
  fill m 13ul 3ul iv
//17-02-08 verification gets slow... cutting code into smaller chunks helps. 

(*
(* local functon, lifted by hand for now *)
private val add: 
  m: matrix -> m0: matrix{disjoint m m0} -> 
  i:u32 { i <^ 16ul } ->
  STL unit
  (requires (fun h -> live h m /\ live h m0))
  (ensures (fun h0 _ h1 -> 
    live h0 m /\ live h0 m0 /\ live h1 m /\ modifies_1 m h0 h1 /\
    as_seq h1 m == Seq.upd 
      (as_seq h0 m) (v i) 
      (Spec.add (as_seq h0 m) (as_seq h0 m0) (v i))
  ))
let add m m0 i = m.(i) <- m.(i) +%^ m0.(i)
*)

private val map2_inplace: 
  #a:eqtype -> 
  f:(a -> a -> Tot a) -> 
  n: UInt32.t ->
  b: buffer a {length b = v n} ->
  b0: buffer a {length b0 = v n /\ disjoint b b0} ->
  STL unit
  (requires (fun h -> live h b /\ live h b0))
  (ensures (fun h0 _ h1 ->
    live h0 b /\ live h0 b0 /\live h1 b /\ modifies_1 b h0 h1 /\
    Seq.equal (as_seq h1 b) (Spec.map2 f (as_seq h0 b) (as_seq h0 b0)))) 
let rec map2_inplace #a f n b b0 = 
  if n <> 0ul then (
    b.(0ul) <- f b.(0ul) b0.(0ul);
    let v1 = b.(0ul) in
    map2_inplace f (n -^ 1ul) (offset b 1ul) (offset b0 1ul);
    let v2 = b.(0ul) in
    assume(v1 = v2) // which lemma to apply??
  )
    // let b' = sub b 1ul n in 
    // let b0' = sub b0 1ul n in
    // assert(disjoint (sub b 0ul 1ul) b');
    // let h0 = ST.get() in 
    // let h1 = ST.get() in 
    // let h2 = ST.get() in
    //let v'' = (sub b0 0ul 1ul).(0ul) in assert(v' = v'');
    //lemma_sub_spec b 0ul 1ul h2;
    //lemma_sub_spec b 0ul 1ul h1;
    //
    // assert(Seq.equal (as_seq h2 b') (Spec.map2 f (as_seq h1 b') (as_seq h1 b0')));
    // assert(Seq.equal (as_seq h2 b) (Seq.cons v (as_seq h2 b')));

private val sum_matrixes: 
  m: matrix -> m0:matrix{disjoint m m0} -> 
  STL unit
  (requires (fun h -> live h m /\ live h m0))
  (ensures (fun h0 _ h1 ->
    live h0 m /\ live h0 m0 /\ live h1 m /\ modifies_1 m h0 h1 /\ 
    as_seq h1 m = Spec.add_state (as_seq h0 m) (as_seq h0 m0) 
    ))
let sum_matrixes m m0 = map2_inplace (fun x y -> x +%^ y) 16ul m m0

(* this split did not help much...
private val chacha20_update: 
  output:bytes -> 
  state:uint32s{length state = 32 /\ disjoint state output} ->
  len:u32{v len <= 64 /\ length output = v len} -> STL unit
    (requires (fun h -> live h state /\ live h output))  
    (ensures (fun h0 _ h1 -> 
      live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 /\
      as_seq h1 output = Seq.slice (Spec.chacha20 key iv c) 0 (v len) ))
let chacha20_update output state len =
  (* Initial state *) 
  let h0 = ST.get() in 
  let m  = sub state  0ul 16ul in
  let m0 = sub state 16ul 16ul in // do we ever rely on m and m0 being contiguous?
  blit m 0ul m0 0ul 16ul; (* save initial state *)
  let h1 = ST.get() in 
  assert(as_seq h1 m = Spec.init (as_seq h0 key) (as_seq h0 iv) c);
  rounds m;
  sum_matrixes m m0; (* add initial and final state *)
  let h2 = ST.get() in 
  assert(as_seq h2 m = Spec.chacha20 (as_seq h0 key) (as_seq h0 iv) c);
  bytes_of_uint32s output m len   (* serialize result into byte stream *)
// avoid this copy when XORing? merge the sum_matrix and output loops? we don't use m0 afterward. 
*)

// computes one pseudo-random 64-byte block 
// (consider fixing len to 64ul)

//17-02-09 TODO this function is not yet fully specified. 
val chacha20: 
  output:bytes -> 
  k:key ->
  n:iv ->
  counter: u32 ->
  len:u32{v len <= Spec.blocklen /\ v len <= length output} -> STL unit
    (requires (fun h -> live h k /\ live h n /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 ))
let chacha20 output key iv c len = 
  let h0 = ST.get() in 

  push_frame ();
  let m = create 0ul 16ul in
  let m0 = create 0ul 16ul in
  chacha20_init m key iv c;
  blit m 0ul m0 0ul 16ul; (* save initial state *)
  let h1 = ST.get() in 
  //assume(as_seq h1 m = Spec.init (as_seq h0 key) (as_seq h0 iv) c);

  // failing; the post of blit is probably too complicated
  //assume(Seq.slice (as_seq h1 m0) 0ul 16ul = Seq.slice (as_seq h1 m) 0ul 16ul);
  //assume(as_seq h1 m0 = Spec.init (as_seq h0 key) (as_seq h0 iv) c);

  rounds m;
  sum_matrixes m m0; (* add initial and final state *)
  let h2 = ST.get() in 
  //assume(as_seq h2 m = Spec.compute (as_seq h0 key) (as_seq h0 iv) c);

  bytes_of_uint32s output m len;   (* serialize result into byte stream *)
  let h3= ST.get() in
  //assume(as_seq h3 output = Spec.chacha20 (v len) (as_seq h0 key) (as_seq h0 iv) c);
  
  pop_frame ()
  
  
// Performance: it may be easier to precompute and re-use an expanded key (m0), 
// to avoid passing around (key, counter, iv, constant), and only have m on the stack.
// We may also merge the 3 final loops: sum_matrixes, bytes_of_uint32s, and outer XOR/ADD. 


(*** Counter-mode Encryption ***)

// The rest of this code is not specific to chacha20.
// It is parameterized by the initial counter (0, or 1 for some AEAD)
// and the block length (here 64 bytes).
// It should appear after PRF idealization.

private let prf = chacha20
private let blocklen = UInt32.uint_to_t Spec.blocklen
// XOR-based encryption and decryption (just swap ciphertext and plaintext)
val counter_mode: 
  k:key -> n:iv -> counter:u32 -> 
  len:u32{v counter + v len / Spec.blocklen < pow2 32} ->
  plaintext:bytes {length plaintext = v len /\ disjoint k plaintext} -> 
  ciphertext:bytes {length ciphertext = v len /\ disjoint n ciphertext /\ disjoint k ciphertext /\ disjoint plaintext ciphertext} -> 
  STL unit
    (requires (fun h -> live h ciphertext /\ live h k /\ live h n /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))

#reset-options "--z3rlimit 100"
// a bit slow, e.g. on the len precondition

let rec counter_mode key iv counter len plaintext ciphertext =
  if len <> 0ul then
  if len <^ blocklen 
  then (* encrypt final partial block *)
    begin
      let cipher = sub ciphertext  0ul len in 
      let plain  = sub plaintext   0ul len in 
      prf cipher key iv counter len;
      xor_bytes_inplace cipher plain len
    end
  else (* encrypt full block *)
    begin
      let cipher = sub ciphertext  0ul blocklen in
      let plain  = sub plaintext   0ul blocklen in
      prf cipher key iv counter blocklen;
      xor_bytes_inplace cipher plain blocklen;
      let len = len -^ blocklen in
      let ciphertext = sub ciphertext blocklen len in
      let plaintext  = sub plaintext  blocklen len in
      counter_mode key iv (counter +^ 1ul) len plaintext ciphertext
    end

