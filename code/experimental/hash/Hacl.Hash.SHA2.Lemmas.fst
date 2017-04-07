module Hacl.Hash.SHA2.Lemmas

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open C.Loops

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let lemma_aux_0 (t:UInt32.t{UInt32.v t >= 16 /\ UInt32.v t < 64}) : Lemma
  (UInt32.v (t -^ 16ul) >= 0 /\ UInt32.v (t -^ 15ul) >= 0
   /\ UInt32.v (t -^ 7ul) >= 0 /\ UInt32.v (t -^ 2ul) >= 0
   /\ UInt32.v (t -^ 16ul) < 64 /\ UInt32.v (t -^ 15ul) < 64
   /\ UInt32.v (t -^ 7ul) < 64 /\ UInt32.v (t -^ 2ul) < 64)
  = ()


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

val lemma_ws_def_0: (b:Spec.SHA2.block_w) -> (t:Spec.SHA2.counter{t < 16}) -> Lemma
  (Spec.SHA2.ws b t = Seq.index b t)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"
let lemma_ws_def_0 b t = ()


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

val lemma_ws_def_1: (b:Spec.SHA2.block_w) -> (t:Spec.SHA2.counter{16 <= t /\ t < 64}) -> Lemma
  (Spec.SHA2.ws b t =
    (let open Spec.SHA2 in
     let t16 = ws b (t - 16) in
     let t15 = ws b (t - 15) in
     let t7  = ws b (t - 7) in
     let t2  = ws b (t - 2) in
     let s1 = _sigma1 t2 in
     let s0 = _sigma0 t15 in
     s1 +%^ (t7 +%^ (s0 +%^ t16))))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"
let lemma_ws_def_1 b t = ()


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let lemma_modifies_0_is_modifies_1 (#a:Type) (h:HyperStack.mem) (b:buffer a{live h b}) : Lemma
  (modifies_1 b h h) =
  lemma_intro_modifies_1 b h h


let lemma_blit_slices_eq (#t:Type) (h0:HyperStack.mem) (h1:HyperStack.mem) (a:buffer t{live h1 a}) (b:buffer t{live h0 b}) (len:nat{len = length a /\ len = length b}): Lemma
  (requires (let slice_a = Seq.slice (as_seq h1 a) 0 len in
             let slice_b = Seq.slice (as_seq h0 b) 0 len in
             slice_a == slice_b))
  (ensures  (as_seq h1 a == as_seq h0 b)) =
  Seq.lemma_eq_intro (as_seq h1 a) (Seq.slice (as_seq h1 a) 0 len);
  Seq.lemma_eq_intro (as_seq h0 b) (Seq.slice (as_seq h0 b) 0 len)


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

val lemma_update_multi_def: (hash:Spec.SHA2.hash_w) -> (blocks:Spec.SHA2.bytes{Seq.length blocks % Spec.SHA2.size_block = 0}) -> Lemma
  (Spec.SHA2.update_multi hash blocks = (
               if Seq.length blocks = 0 then hash
               else (
                 let (block,rem) = Seq.split blocks Spec.SHA2.size_block in
                 let hash = Spec.SHA2.update hash block in
                 Spec.SHA2.update_multi hash rem)))

#reset-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 20"

let lemma_update_multi_def hash blocks = ()
 
