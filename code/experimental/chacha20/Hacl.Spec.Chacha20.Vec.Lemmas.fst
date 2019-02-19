module Hacl.Spec.Chacha20.Vec.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.IntVector
module Scalar = Spec.Chacha20
open Hacl.Spec.Chacha20.Vec

#set-options "--max_fuel 1 --z3rlimit 300"

val line_lemma: #w:lanes -> a:idx -> b:idx -> d:idx -> 
			   s:rotval U32 -> m:state w ->
    Lemma (transpose_state (line #w a b d s m) == 
	   map (Scalar.line a b d s) (transpose_state m))


let line_lemma #w a b d s m = 
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
  | 8 -> 
    assert (equal (transpose_state (line #w a b d s m)).[0] (Scalar.line a b d s (transpose_state m).[0])); 
    assert (equal (transpose_state (line #w a b d s m)).[1] (Scalar.line a b d s (transpose_state m).[1])); 
    assert (equal (transpose_state (line #w a b d s m)).[2] (Scalar.line a b d s (transpose_state m).[2])); 
    assert (equal (transpose_state (line #w a b d s m)).[3] (Scalar.line a b d s (transpose_state m).[3])); 
    assert (equal (transpose_state (line #w a b d s m)).[4] (Scalar.line a b d s (transpose_state m).[4])); 
    assert (equal (transpose_state (line #w a b d s m)).[5] (Scalar.line a b d s (transpose_state m).[5])); 
    assert (equal (transpose_state (line #w a b d s m)).[6] (Scalar.line a b d s (transpose_state m).[6])); 
    assert (equal (transpose_state (line #w a b d s m)).[7] (Scalar.line a b d s (transpose_state m).[7])); 
    assert (equal (transpose_state (line #w a b d s m)) (map (Scalar.line a b d s) (transpose_state m)))


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

val sum_state_lemma: #w:lanes -> st1:state w -> st2:state w -> 
    Lemma (ensures (transpose_state (sum_state st1 st2) ==
		    map2 Scalar.sum_state (transpose_state st1) (transpose_state st2)))
	  [SMTPat (transpose_state (sum_state st1 st2))]
let sum_state_lemma #w st1 st2 =
  match w with
  | 1 -> 
      assert (equal (transpose_state (sum_state st1 st2)).[0]
		      (Scalar.sum_state (transpose_state st1).[0] (transpose_state st2).[0]));
      assert (equal (transpose_state (sum_state st1 st2))
		      (map2 Scalar.sum_state (transpose_state st1) (transpose_state st2)))
  | 4 -> 
      assert (equal (transpose_state (sum_state st1 st2)).[0]
		      (Scalar.sum_state (transpose_state st1).[0] (transpose_state st2).[0]));
      assert (equal (transpose_state (sum_state st1 st2)).[1]
		      (Scalar.sum_state (transpose_state st1).[1] (transpose_state st2).[1]));
      assert (equal (transpose_state (sum_state st1 st2)).[2]
		      (Scalar.sum_state (transpose_state st1).[2] (transpose_state st2).[2]));
      assert (equal (transpose_state (sum_state st1 st2)).[3]
		      (Scalar.sum_state (transpose_state st1).[3] (transpose_state st2).[3]));
      assert (equal (transpose_state (sum_state st1 st2))
		      (map2 (Scalar.sum_state) (transpose_state st1) (transpose_state st2)))
  | 8 -> 
      assert (equal (transpose_state (sum_state st1 st2)).[0]
		      (Scalar.sum_state (transpose_state st1).[0] (transpose_state st2).[0]));
      assert (equal (transpose_state (sum_state st1 st2)).[1]
		      (Scalar.sum_state (transpose_state st1).[1] (transpose_state st2).[1]));
      assert (equal (transpose_state (sum_state st1 st2)).[2]
		      (Scalar.sum_state (transpose_state st1).[2] (transpose_state st2).[2]));
      assert (equal (transpose_state (sum_state st1 st2)).[3]
		      (Scalar.sum_state (transpose_state st1).[3] (transpose_state st2).[3]));
      assert (equal (transpose_state (sum_state st1 st2)).[4]
		      (Scalar.sum_state (transpose_state st1).[4] (transpose_state st2).[4]));
      assert (equal (transpose_state (sum_state st1 st2)).[5]
		      (Scalar.sum_state (transpose_state st1).[5] (transpose_state st2).[5]));
      assert (equal (transpose_state (sum_state st1 st2)).[6]
		      (Scalar.sum_state (transpose_state st1).[6] (transpose_state st2).[6]));
      assert (equal (transpose_state (sum_state st1 st2)).[7]
		      (Scalar.sum_state (transpose_state st1).[7] (transpose_state st2).[7]));
      assert (equal (transpose_state (sum_state st1 st2))
		      (map2 (Scalar.sum_state) (transpose_state st1) (transpose_state st2)))

val add_counter_lemma: #w:lanes -> st:state w -> ctr:counter{w * ctr <= max_size_t} ->
    Lemma (ensures (transpose_state (add_counter #w ctr st) ==
		    map (Scalar.add_counter (w * ctr)) (transpose_state st)))
	  [SMTPat (transpose_state (add_counter #w ctr st))]
let add_counter_lemma #w st ctr =
    assert (uint_v (u32 w *! u32 ctr) == w * ctr);
    assume (u32 (w * ctr) == u32 w *! u32 ctr);
    let tst = transpose_state st in
    let res = add_counter #w ctr st in
    match w with
    | 1 -> 
	assert (equal (transpose_state res).[0]
		      (Scalar.add_counter (w * ctr) tst.[0]));
	assert (equal (transpose_state res)
		      (map (Scalar.add_counter (w * ctr)) (transpose_state st))) 
   | 4 -> 
	assert (equal (transpose_state res).[0]
		      (Scalar.add_counter (w * ctr) tst.[0]));
	assert (equal (transpose_state res).[1]
		      (Scalar.add_counter (w * ctr) tst.[1]));
	assert (equal (transpose_state res).[2]
		      (Scalar.add_counter (w * ctr) tst.[2]));
	assert (equal (transpose_state res).[3]
		      (Scalar.add_counter (w * ctr) tst.[3]));
	assert (equal (transpose_state res)
		      (map (Scalar.add_counter (w * ctr)) (transpose_state st)))
   | 8 -> 
	assert (equal (transpose_state res).[0]
		      (Scalar.add_counter (w * ctr) tst.[0]));
	assert (equal (transpose_state res).[1]
		      (Scalar.add_counter (w * ctr) tst.[1]));
	assert (equal (transpose_state res).[2]
		      (Scalar.add_counter (w * ctr) tst.[2]));
	assert (equal (transpose_state res).[3]
		      (Scalar.add_counter (w * ctr) tst.[3]));
	assert (equal (transpose_state res).[4]
		      (Scalar.add_counter (w * ctr) tst.[4]));
	assert (equal (transpose_state res).[5]
		      (Scalar.add_counter (w * ctr) tst.[5]));
	assert (equal (transpose_state res).[6]
		      (Scalar.add_counter (w * ctr) tst.[6]));
	assert (equal (transpose_state res).[7]
		      (Scalar.add_counter (w * ctr) tst.[7]));
	assert (equal (transpose_state res)
		      (map (Scalar.add_counter (w * ctr)) (transpose_state st)))

val chacha20_core_lemma: #w:lanes -> ctr:counter{w * ctr <= max_size_t} -> s0:state w -> 
    Lemma (ensures (transpose_state (chacha20_core ctr s0) == 
		    map (Scalar.chacha20_core (w * ctr)) (transpose_state s0)))
	  [SMTPat (transpose_state (chacha20_core ctr s0))]
let chacha20_core_lemma #w ctr s0 = 
  assert (transpose_state (chacha20_core ctr s0) ==
	  transpose_state (add_counter ctr (sum_state s0 (rounds (add_counter ctr s0)))));
  assert (transpose_state (chacha20_core ctr s0) ==
	  map (Scalar.add_counter (w * ctr)) 
	  (map2 Scalar.sum_state (transpose_state s0) 
	  (map Scalar.rounds 
	  (map (Scalar.add_counter (w * ctr))
	  (transpose_state s0)))));
  match w with
    | 1 -> assert (equal (transpose_state (chacha20_core ctr s0)).[0] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[0]));
	  assert (equal (transpose_state (chacha20_core ctr s0))
			(map (Scalar.chacha20_core (w * ctr)) (transpose_state s0)))
    | 4 -> assert (equal (transpose_state (chacha20_core ctr s0)).[0] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[0]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[1] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[1]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[2] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[2]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[3] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[3]));
	  assert (equal (transpose_state (chacha20_core ctr s0))
			(map (Scalar.chacha20_core (w * ctr)) (transpose_state s0)))
    | 8 -> assert (equal (transpose_state (chacha20_core ctr s0)).[0] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[0]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[1] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[1]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[2] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[2]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[3] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[3]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[4] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[4]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[5] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[5]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[6] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[6]));
	  assert (equal (transpose_state (chacha20_core ctr s0)).[7] 
			(Scalar.chacha20_core (w * ctr) (transpose_state s0).[7]));
	  assert (equal (transpose_state (chacha20_core ctr s0))
			(map (Scalar.chacha20_core (w * ctr)) (transpose_state s0)))

val chacha20_init_lemma: #w:lanes -> k:key -> n:nonce -> ctr0:counter{ctr0+3 <= max_size_t} -> 
    Lemma (transpose_state (chacha20_init #w k n ctr0) ==
	   map (Scalar.chacha20_init k n) (create4 ctr0 (ctr0+1) (ctr0+2) (ctr0+3)))
let chacha20_init_lemma #w k n ctro = ()

val xor_block_lemma: #w:lanes -> k:state w -> b:blocks w -> 
    Lemma (ensures (
		let res = xor_block k b in
		res == map_blocks_multi size_block w b 
		  (fun i -> Scalar.xor_block (transpose_state k).[i])))
	   [SMTPat (xor_block k b)]
let xor_block_lemma #w k b = admit()    

#set-options "--z3rlimit 50"
val chacha20_encrypt_block_lemma: #w:lanes -> st0:state w -> incr:counter{w * incr <= max_size_t} -> b:blocks w ->
	Lemma (ensures (
		let res = chacha20_encrypt_block st0 incr b in
		let spec = map_blocks_multi size_block w b 
		       (fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr)) in
		res == spec))

#set-options "--z3rlimit 200 --max_ifuel 2"
let chacha20_encrypt_block_lemma #w st0 incr b = 
  assert (chacha20_encrypt_block #w st0 incr b == 
	  xor_block (chacha20_core incr st0) b);
  match w with
  | 1 -> assert (length b == 64);
        assert (equal (chacha20_encrypt_block st0 incr b)
		      (map_blocks_multi size_block w b 
			(fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))))
  | 4 -> assert (length b == 256);
        assert (equal (chacha20_encrypt_block st0 incr b)
		      (map_blocks_multi size_block w b 
		      (fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))))
  | 8 -> assert (length b == 512);
        assert (equal (chacha20_encrypt_block st0 incr b)
		      (map_blocks_multi size_block w b 
		      (fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))))

val chacha20_encrypt_last_lemma: #w:lanes -> st0:state w -> incr:counter{w * incr <= max_size_t} -> (len:size_nat{len < w * size_block}) -> b:lbytes len ->
	Lemma (ensures (
		let res = chacha20_encrypt_last st0 incr len b in
		res == map_blocks size_block b 
		  (fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w*incr))
		  (fun i -> Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w*incr))))

let chacha20_encrypt_last_lemma #w st0 incr len b = 
  assert (chacha20_encrypt_last #w st0 incr len b == 
	  Seq.slice (chacha20_encrypt_block st0 incr 
		    (update_sub (create (w * size_block) (u8 0)) 0 len b)) 0 len); 
  let blocks = len / size_block in
  let rem = len % size_block in
  match w with
  | 1 -> assert (len < 64);
        assert (forall (i:nat). i < size_block * blocks ==>
		  Seq.index (chacha20_encrypt_last st0 incr len b) i ==
		  Seq.index (map_blocks size_block b 
			(fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))
			(fun i -> Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w * incr))) i);
        assert (forall (i:nat). (i >= size_block * blocks /\ i < len) ==>
		  Seq.index (chacha20_encrypt_last st0 incr len b) i ==
		  Seq.index (Scalar.chacha20_encrypt_last (transpose_state st0).[blocks] (w * incr) rem 
							  (Seq.slice b (blocks * size_block) len)) (i % size_block));
	admit();
        assert (forall (i:nat). (i >= size_block * blocks /\ i < len) ==>
		  Seq.index (chacha20_encrypt_last st0 incr len b) i ==
		  Seq.index (map_blocks size_block b 
			(fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))
			(fun i -> Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w * incr))) i);

	admit()
  | _ -> admit()


(*
        assert (forall (i:nat). i / size_block < blocks ==>
		      Seq.index (chacha20_encrypt_last st0 incr len b) i ==`
		      Seq.index (map_blocks size_block b 
			(fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))
			(fun i -> Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w * incr))) i);
	admit()

*)


let chacha20_update_lemma (st0: Scalar.state) (msg: bytes{length msg / size_block + v st0.[12] <= max_size_t}) =
  let len = length msg in
  let blocks = len / (4*size_block) in
  let rem = len % (4*size_block) in

  
  admit();
  assert (Scalar.chacha20_update st0 msg ==
	  map_blocks size_block msg
	    (Scalar.chacha20_encrypt_block st0)
	    (Scalar.chacha20_encrypt_last st0));
  assert (forall (i:nat). i < 4 * size_block * blocks ==>
	 Seq.index 
	  (map_blocks size_block msg
	    (Scalar.chacha20_encrypt_block st0)
	    (Scalar.chacha20_encrypt_last st0)) i ==
	 Seq.index (Scalar.chacha20_encrypt_block st0 (i/size_block) (Seq.slice msg (i*size_block) ((i+1)*size_block))) (i % size_block));
  assert (Seq.equal 
	  (map_blocks size_block msg
	    (Scalar.chacha20_encrypt_block st0)
	    (Scalar.chacha20_encrypt_last st0))
	  (map_blocks (4*size_block) msg
	    (fun i b4 -> 
	      map_blocks_multi size_block 4 b4 
		(fun j b -> Scalar.chacha20_encrypt_block (Scalar.add_counter j st0) (4*i) b))
            (fun i l b4 ->
	      map_blocks size_block b4 
		(fun j b -> Scalar.chacha20_encrypt_block (Scalar.add_counter j st0) (4*i) b)
		(fun j l b -> Scalar.chacha20_encrypt_last (Scalar.add_counter j st0) (4*i) l b))))


val chacha20_encrypt_bytes_lemma: #w:lanes -> 
    k:key -> n:nonce -> c:counter -> 
    msg:bytes{length msg/size_block + c <= max_size_t} ->
    Lemma (chacha20_encrypt_bytes #w k n c msg == 
	   Scalar.chacha20_encrypt_bytes k n c msg)
