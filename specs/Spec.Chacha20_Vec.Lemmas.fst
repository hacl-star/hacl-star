module Spec.Chacha20_Vec.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.IntVector
module Scalar = Spec.Chacha20
open Spec.Chacha20_Vec

#set-options "--max_fuel 1 --z3rlimit 200"

val line_lemma: #w:lanes -> a:idx -> b:idx -> d:idx -> s:rotval U32 -> m:state w ->
  Lemma (ensures (transpose_state (line #w a b d s m) == map (Scalar.line a b d s) (transpose_state m)))
	[SMTPat (transpose_state (line #w a b d s m))]
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

val add_counter_lemma: #w:lanes -> st:state w -> ctr:counter{w * ctr <= max_size_t} ->
    Lemma (ensures (transpose_state (add_counter #w st ctr) ==
		    map (fun st -> st.[12] <- st.[12] +. u32 (w * ctr)) (transpose_state st)))
	  [SMTPat (transpose_state (add_counter #w st ctr))]

val chacha20_core_lemma: #w:lanes -> s0:state w -> ctr:counter{w * ctr <= max_size_t} -> 
    Lemma (ensures (transpose_state (chacha20_core s0 ctr) == 
		    map (fun s -> Scalar.chacha20_core s (w * ctr)) (transpose_state s0)))
	  [SMTPat (transpose_state (chacha20_core s0 ctr))]
let chacha20_core_lemma #w s0 ctr = admit()
    
val chacha20_init_lemma: #w:lanes -> k:key -> n:nonce -> ctr0:counter{ctr0+3 <= max_size_t} -> 
    Lemma (transpose_state (chacha20_init #w k n ctr0) ==
	   map (Scalar.chacha20_init k n) (create4 ctr0 (ctr0+1) (ctr0+2) (ctr0+3)))
let chacha20_init_lemma #w k n ctro = admit()
