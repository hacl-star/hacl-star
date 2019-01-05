module Spec.Chacha20_Vec

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.IntVector
module Scalar = Spec.Chacha20

#set-options "--max_fuel 1 --z3rlimit 200"

/// Constants and Types

let size_key = 32
let size_block = 64
let size_nonce = 12

(* TODO: Remove, left here to avoid breaking implementation *)
let keylen = 32   (* in bytes *)
let blocklen = 64 (* in bytes *)
let noncelen = 12 (* in bytes *)

type key = lbytes size_key
type block1 = lbytes size_block
type nonce = lbytes size_nonce
type counter = size_nat
type subblock = b:bytes{length b <= size_block}

// Internally, blocks are represented as 16 x 4-byte integers
let lanes = n:width{n == 1 \/ n == 4 \/ n == 8}
let uint32xN (w:lanes) = vec_t U32 w
type state (w:lanes) = lseq (uint32xN w) 16
type idx = n:size_nat{n < 16}
type shuffle (w:lanes) = state w -> state w
type blocks (w:lanes) = lbytes (w * 64)

// Using @ as a functional substitute for ;
let op_At f g = fun x -> g (f x)


/// Specification

let transpose_state (#w:lanes) (st:state w) : lseq (lseq uint32 16) w  = 
  createi w (fun i -> 
	  let x : lseq uint32 16 = create16 (vec_v st.[0]).[i] (vec_v st.[1]).[i] (vec_v st.[2]).[i] (vec_v st.[3]).[i]
			    (vec_v st.[4]).[i] (vec_v st.[5]).[i] (vec_v st.[6]).[i] (vec_v st.[7]).[i]
			    (vec_v st.[8]).[i] (vec_v st.[9]).[i] (vec_v st.[10]).[i] (vec_v st.[11]).[i]
			    (vec_v st.[12]).[i] (vec_v st.[13]).[i] (vec_v st.[14]).[i] (vec_v st.[15]).[i] in
	  x)
  

let line (#w:lanes) (a:idx) (b:idx) (d:idx) (s:rotval U32) (m:state w) : state w =
  let m = m.[a] <- (m.[a] +| m.[b]) in
  let m = m.[d] <- ((m.[d] ^| m.[a]) <<<| s) in m

val line_map_lemma: #w:lanes -> a:idx -> b:idx -> d:idx -> s:rotval U32 -> m:state w ->
  Lemma (ensures (transpose_state (line #w a b d s m) == map (Scalar.line a b d s) (transpose_state m)))
	[SMTPat (transpose_state (line #w a b d s m))]
let line_map_lemma #w a b d s m = 
  match w with
  | 1 -> 
    assert (equal (transpose_state (line #w a b d s m)).[0] (Scalar.line a b d s (transpose_state m).[0])); 
    assert (equal (transpose_state (line #w a b d s m)) (map (Scalar.line a b d s) (transpose_state m)))
  | 4 -> 
    assert (equal (transpose_state (line #w a b d s m)).[0] (Scalar.line a b d s (transpose_state m).[0])); 
    assert (equal (transpose_state (line #w a b d s m)).[1] (Scalar.line a b d s (transpose_state m).[1])); 
    assert (equal (transpose_state (line #w a b d s m)).[2] (Scalar.line a b d s (transpose_state m).[2])); 
    assert (equal (transpose_state (line #w a b d s m)).[3] (Scalar.line a b d s (transpose_state m).[3])); 
    assert (equal (transpose_state (line #w a b d s m)) (map (Scalar.line a b d s) (transpose_state m)))
  | 8 -> admit();
    assert (equal (transpose_state (line #w a b d s m)).[0] (Scalar.line a b d s (transpose_state m).[0])); 
    assert (equal (transpose_state (line #w a b d s m)).[1] (Scalar.line a b d s (transpose_state m).[1])); 
    assert (equal (transpose_state (line #w a b d s m)).[2] (Scalar.line a b d s (transpose_state m).[2])); 
    assert (equal (transpose_state (line #w a b d s m)).[3] (Scalar.line a b d s (transpose_state m).[3])); 
    assert (equal (transpose_state (line #w a b d s m)).[4] (Scalar.line a b d s (transpose_state m).[4])); 
    assert (equal (transpose_state (line #w a b d s m)).[5] (Scalar.line a b d s (transpose_state m).[5])); 
    assert (equal (transpose_state (line #w a b d s m)).[6] (Scalar.line a b d s (transpose_state m).[6])); 
    assert (equal (transpose_state (line #w a b d s m)).[7] (Scalar.line a b d s (transpose_state m).[7])); 
    assert (equal (transpose_state (line #w a b d s m)) (map (Scalar.line a b d s) (transpose_state m)))


let quarter_round (#w:lanes) a b c d : shuffle w =
  line a b d (size 16) @
  line c d b (size 12) @
  line a b d (size 8)  @
  line c d b (size 7)

val quarter_round_map_lemma: #w:lanes -> a:idx -> b:idx -> c:idx -> d:idx -> m:state w ->
  Lemma (ensures (transpose_state (quarter_round #w a b c d m) == map (Scalar.quarter_round a b c d) (transpose_state m)))
	[SMTPat (transpose_state (quarter_round #w a b c d m))]
let quarter_round_map_lemma #w a b c d m = 
  match w with
  | 1 ->  
       assert (transpose_state (quarter_round #w a b c d m) == map (Scalar.line c d b 7ul) (transpose_state (line #w a b d 8ul (line #w c d b 12ul (line #w a b d 16ul m)))));
       assert (equal (transpose_state (quarter_round #w a b c d m)) (map (Scalar.quarter_round a b c d) (transpose_state m)))
  | 4 ->  
       assert (transpose_state (quarter_round #w a b c d m) == map (Scalar.line c d b 7ul) (transpose_state (line #w a b d 8ul (line #w c d b 12ul (line #w a b d 16ul m)))));
       assert (equal (transpose_state (quarter_round #w a b c d m)) (map (Scalar.quarter_round a b c d) (transpose_state m)))
  | 8 ->  
       assert (transpose_state (quarter_round #w a b c d m) == map (Scalar.line c d b 7ul) (transpose_state (line #w a b d 8ul (line #w c d b 12ul (line #w a b d 16ul m)))));
       assert (equal (transpose_state (quarter_round #w a b c d m)) (map (Scalar.quarter_round a b c d) (transpose_state m)))
  
let column_round (#w:lanes) : shuffle w =
  quarter_round 0 4 8  12 @
  quarter_round 1 5 9  13 @
  quarter_round 2 6 10 14 @
  quarter_round 3 7 11 15

let diagonal_round (#w:lanes) : shuffle w =
  quarter_round 0 5 10 15 @
  quarter_round 1 6 11 12 @
  quarter_round 2 7 8  13 @
  quarter_round 3 4 9  14

let double_round (#w:lanes) : shuffle w =
  column_round @ diagonal_round (* 2 rounds *)

val double_round_map_lemma: #w:lanes -> m:state w -> 
  Lemma (ensures (transpose_state (double_round #w m) == map (Scalar.double_round) (transpose_state m)))
	[SMTPat (transpose_state (double_round #w m))]
let double_round_map_lemma #w m = 
  match w with
  | 1 ->  	
       assert (transpose_state (double_round #w m) == 
	      map (Scalar.quarter_round 3 4 9 14) 
		(transpose_state 
		  (quarter_round 2 7 8 13
		  (quarter_round 1 6 11 12
		  (quarter_round 0 5 10 15
		  (quarter_round 3 7 11 15
		  (quarter_round 2 6 10 14
		  (quarter_round 1 5 9 13
		  (quarter_round 0 4 8 12
		  m)))))))));
assert (equal (transpose_state (double_round #w m)) (map (Scalar.double_round) (transpose_state m)))
  | 4 -> 
       assert (transpose_state (double_round #w m) == 
	      map (Scalar.quarter_round 3 4 9 14) 
		(transpose_state 
		  (quarter_round 2 7 8 13
		  (quarter_round 1 6 11 12
		  (quarter_round 0 5 10 15
		  (quarter_round 3 7 11 15
		  (quarter_round 2 6 10 14
		  (quarter_round 1 5 9 13
		  (quarter_round 0 4 8 12
		  m)))))))));
	assert (equal (transpose_state (double_round #w m)) (map (Scalar.double_round) (transpose_state m)))
  | 8 -> 
         assert (transpose_state (double_round #w m) == 
	      map (Scalar.quarter_round 3 4 9 14) 
		(transpose_state 
		  (quarter_round 2 7 8 13
		  (quarter_round 1 6 11 12
		  (quarter_round 0 5 10 15
		  (quarter_round 3 7 11 15
		  (quarter_round 2 6 10 14
		  (quarter_round 1 5 9 13
		  (quarter_round 0 4 8 12
		  m)))))))));
	assert (equal (transpose_state (double_round #w m)) (map (Scalar.double_round) (transpose_state m)))


let rounds (#w:lanes) (m:state w) : state w =
  double_round (double_round (
  double_round (double_round (
  double_round (double_round (
  double_round (double_round (
  double_round (double_round m)))))))))

let scalar_rounds (m:Scalar.state) : Scalar.state = 
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round m)))))))))
  
val scalar_rounds_unroll_lemma: m:Scalar.state -> 
    Lemma (scalar_rounds m == Scalar.rounds m)
	  [SMTPat (Scalar.rounds m)]
let scalar_rounds_unroll_lemma m = 
    eq_repeat0 Scalar.double_round m;
    unfold_repeat 10 Scalar.double_round m 0;
    unfold_repeat 10 Scalar.double_round m 1;
    unfold_repeat 10 Scalar.double_round m 2;
    unfold_repeat 10 Scalar.double_round m 3;
    unfold_repeat 10 Scalar.double_round m 4;
    unfold_repeat 10 Scalar.double_round m 5;
    unfold_repeat 10 Scalar.double_round m 6;
    unfold_repeat 10 Scalar.double_round m 7;
    unfold_repeat 10 Scalar.double_round m 8;
    unfold_repeat 10 Scalar.double_round m 9;
    ()
	  
val rounds_lemma: #w:lanes -> m:state w -> 
  Lemma (ensures (transpose_state (rounds #w m) == map Scalar.rounds (transpose_state m)))
	[SMTPat (transpose_state (rounds #w m))]
let rounds_lemma #w m =
    assert (transpose_state (rounds #w m) == 
	    map (Scalar.double_round) (transpose_state (double_round (
    	    double_round (double_round (
	    double_round (double_round ( 
    	    double_round (double_round (
	    double_round (double_round m)))))))))));
    assert (transpose_state (rounds #w m) == 
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (
	    map (Scalar.double_round) (transpose_state m)))))))))));
    match w with
    | 1 -> 
	assert (equal (transpose_state (rounds #w m)).[0] (Scalar.rounds (transpose_state m).[0]));
	assert (equal (transpose_state (rounds #w m)) (map (Scalar.rounds) (transpose_state m)))
    | 4 -> 
	assert (equal (transpose_state (rounds #w m)).[0] (Scalar.rounds (transpose_state m).[0]));
	assert (equal (transpose_state (rounds #w m)).[1] (Scalar.rounds (transpose_state m).[1]));
	assert (equal (transpose_state (rounds #w m)).[2] (Scalar.rounds (transpose_state m).[2]));
	assert (equal (transpose_state (rounds #w m)).[3] (Scalar.rounds (transpose_state m).[3]));
	assert (equal (transpose_state (rounds #w m)) (map (Scalar.rounds) (transpose_state m)))
    | 8 -> 
	assert (equal (transpose_state (rounds #w m)).[0] (Scalar.rounds (transpose_state m).[0]));
	assert (equal (transpose_state (rounds #w m)) (map (Scalar.rounds) (transpose_state m)))


let sum_state (#w:lanes) (st1:state w) (st2:state w) : state w =
  map2 (+|) st1 st2 

val sum_state_lemma: #w:lanes -> st1:state w -> st2:state w -> 
    Lemma (ensures (transpose_state (sum_state st1 st2) ==
		    map2 (map2 (+.)) (transpose_state st1) (transpose_state st2)))
let sum_state_lemma #w st1 st2 =
  match w with
  | 1 -> 
      assert (equal (transpose_state (sum_state st1 st2)).[0]
		      (map2 (+.) (transpose_state st1).[0] (transpose_state st2).[0]));
      assert (equal (transpose_state (sum_state st1 st2))
		      (map2 (map2 (+.)) (transpose_state st1) (transpose_state st2)))
  | 4 -> 
      assert (equal (transpose_state (sum_state st1 st2)).[0]
		      (map2 (+.) (transpose_state st1).[0] (transpose_state st2).[0]));
      assert (equal (transpose_state (sum_state st1 st2)).[1]
		      (map2 (+.) (transpose_state st1).[1] (transpose_state st2).[1]));
      assert (equal (transpose_state (sum_state st1 st2)).[2]
		      (map2 (+.) (transpose_state st1).[2] (transpose_state st2).[2]));
      assert (equal (transpose_state (sum_state st1 st2)).[3]
		      (map2 (+.) (transpose_state st1).[3] (transpose_state st2).[3]));
      assert (equal (transpose_state (sum_state st1 st2))
		      (map2 (map2 (+.)) (transpose_state st1) (transpose_state st2)))
  | 8 -> 
      assert (equal (transpose_state (sum_state st1 st2)).[0]
		      (map2 (+.) (transpose_state st1).[0] (transpose_state st2).[0]));
      assert (equal (transpose_state (sum_state st1 st2)).[1]
		      (map2 (+.) (transpose_state st1).[1] (transpose_state st2).[1]));
      assert (equal (transpose_state (sum_state st1 st2)).[2]
		      (map2 (+.) (transpose_state st1).[2] (transpose_state st2).[2]));
      assert (equal (transpose_state (sum_state st1 st2)).[3]
		      (map2 (+.) (transpose_state st1).[3] (transpose_state st2).[3]));
      assert (equal (transpose_state (sum_state st1 st2)).[4]
		      (map2 (+.) (transpose_state st1).[4] (transpose_state st2).[4]));
      assert (equal (transpose_state (sum_state st1 st2)).[5]
		      (map2 (+.) (transpose_state st1).[5] (transpose_state st2).[5]));
      assert (equal (transpose_state (sum_state st1 st2)).[6]
		      (map2 (+.) (transpose_state st1).[6] (transpose_state st2).[6]));
      assert (equal (transpose_state (sum_state st1 st2)).[7]
		      (map2 (+.) (transpose_state st1).[7] (transpose_state st2).[7]));
      assert (equal (transpose_state (sum_state st1 st2))
		      (map2 (map2 (+.)) (transpose_state st1) (transpose_state st2)))

let add_counter (#w:lanes) (st:state w) (ctr:counter{w * ctr <= max_size_t}) : state w =
  let cv = vec_load (u32 w *! u32 ctr) w in
  st.[12] <- st.[12] +| cv 

val add_counter_lemma: #w:lanes -> st:state w -> ctr:counter{w * ctr <= max_size_t} ->
    Lemma (ensures (transpose_state (add_counter #w st ctr) ==
		    map (fun st -> st.[12] <- st.[12] +. u32 (w * ctr)) (transpose_state st)))
	  [SMTPat (transpose_state (add_counter #w st ctr))]


let chacha20_core (#w:lanes) (s0:state w) (ctr:counter{w * ctr <= max_size_t}) : state w =
  let k = add_counter s0 ctr in
  let k = rounds k in
  let k = sum_state k s0 in
  add_counter k ctr

val chacha20_core_lemma: #w:lanes -> s0:state w -> ctr:counter{w * ctr <= max_size_t} -> 
    Lemma (ensures (transpose_state (chacha20_core s0 ctr) == 
		    map (fun s -> Scalar.chacha20_core s (w * ctr)) (transpose_state s0)))
	  [SMTPat (transpose_state (chacha20_core s0 ctr))]
let chacha20_core_lemma #w s0 ctr = admit()
    
    
inline_for_extraction
let c0 = 0x61707865ul
inline_for_extraction
let c1 = 0x3320646eul
inline_for_extraction
let c2 = 0x79622d32ul
inline_for_extraction
let c3 = 0x6b206574ul

let chacha20_constants : lseq size_t 4 = 
  [@ inline_let]
  let l = [c0;c1;c2;c3] in
  assert_norm(List.Tot.length l == 4);
  createL l
  
let setup1 (k:key) (n:nonce) (ctr0:counter) : lseq uint32 16 = 
  Scalar.setup k n ctr0 (create 16 (u32 0))

inline_for_extraction
let vec_load_i (#t:v_inttype) (w:width) (x:uint_t t SEC) = vec_load #t x w

let chacha20_init (#w:lanes) (k:key) (n:nonce) (ctr0:counter) : state w = 
  let st1 = setup1 k n ctr0 in
  let st = map (vec_load_i w) st1 in
  let c = vec_counter U32 w in
  st.[12] <- st.[12] +| c

val chacha20_init_lemma: #w:lanes -> k:key -> n:nonce -> ctr0:counter{ctr0+3 <= max_size_t} -> 
    Lemma (transpose_state (chacha20_init #w k n ctr0) ==
	   map (Scalar.chacha20_init k n) (create4 ctr0 (ctr0+1) (ctr0+2) (ctr0+3)))
let chacha20_init_lemma #w k n ctro = admit()

let transpose_store_blocks (#w:lanes) (st:state w) : lseq uint32 (w * 16)  = 
  createi (w * 16) (fun i -> (vec_v st.[i % 16]).[i / 16]) 

let store_blocks (#w:lanes) (st:state w) : lseq uint32 (w * 16)  = 
  createi (w * 16) (fun i -> (vec_v st.[i / w]).[i % w]) 

let load_blocks1 (sq:lseq uint32 16) : state 1 = 
  createi 16 (fun i -> vec_load sq.[i] 1)

let load_blocks4 (sq:lseq uint32 64) : state 4 = 
  createi 16 (fun i -> vec_load4 sq.[4*i] sq.[4*i+1] sq.[4*i+2] sq.[4*i+3])

let load_blocks8 (sq:lseq uint32 128) : state 8 = 
  createi 16 (fun i -> vec_load8 sq.[8*i] sq.[8*i+1] sq.[8*i+2] sq.[8*i+3] 
			      sq.[8*4] sq.[8*i+5] sq.[8*i+6] sq.[8*i+7])

let load_blocks (#w:lanes) (sq:lseq uint32 (w * 16)) : state w = 
  match w with
  | 1 -> load_blocks1 sq
  | 4 -> load_blocks4 sq
  | 8 -> load_blocks8 sq

let transpose (#w:lanes) (st:state w) : state w = 
  load_blocks (transpose_store_blocks st)
  
let chacha20_key_block0 (#w:lanes) (k:key) (n:nonce) : Tot block1 =
  let st = chacha20_init #w k n 0 in
  let kb = transpose_store_blocks st in
  uints_to_bytes_le (sub kb 0 16)

let xor_block (#w:lanes) (k:state w) (b:blocks w) : blocks w  = 
  let iby = uints_from_bytes_le b in
  let ib = load_blocks iby in 
  let kb = transpose k in
  let ob = map2 (^|) ib kb in
  let oby = store_blocks ob in
  uints_to_bytes_le oby

let chacha20_encrypt_block (#w:lanes) (st0:state w) (incr:counter) (b:blocks w) : blocks w =
  let k = chacha20_core st0 incr in
  xor_block k b
  
let chacha20_encrypt_last
  (#w:lanes)
  (st0: state w)
  (incr: counter)
  (len: size_nat{len < w * size_block})
  (b: lbytes len) :
  Tot (lbytes len) =

  let plain = create (w * size_block) (u8 0) in
  let plain = update_sub plain 0 len b in
  let cipher = chacha20_encrypt_block st0 incr plain in
  sub cipher 0 (length b)


val chacha20_update:
    #w:lanes
  -> st0: state w
  -> msg: bytes{length msg / (w * size_block)  <= max_size_t}
  -> cipher: bytes{length cipher == length msg}
let chacha20_update #w st0 msg = 
  let cipher = msg in
  map_blocks (w * size_block) cipher
    (chacha20_encrypt_block st0)
    (chacha20_encrypt_last st0)


val chacha20encrypt_bytes:
    #w:lanes
  -> k: key
  -> n: nonce
  -> c: counter
  -> msg: bytes{length msg / (w * size_block) <= max_size_t}
  -> cipher: bytes{length cipher == length msg}

let chacha20_encrypt_bytes #w key nonce ctr0 msg =
  let st0 = chacha20_init #w key nonce ctr0 in
  chacha20_update #w st0 msg

val chacha20_decrypt_bytes:
    #w:lanes
  -> k: key
  -> n: nonce
  -> c: counter
  -> cipher: bytes{length cipher / (w * size_block) <= max_size_t}
  -> msg: bytes{length cipher == length msg}

let chacha20_decrypt_bytes #w key nonce ctr0 cipher =
  let st0 = chacha20_init #w key nonce ctr0 in
  chacha20_update #w st0 cipher
