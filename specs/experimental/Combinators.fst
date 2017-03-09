module Combinators

open FStar.Mul
open FStar.ST
open FStar.Buffer
(* open C.Loops *)

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module UInt32 = FStar.UInt32

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(* Missing operators on maps with quantified specifications *)

val seq_map:
  #a:Type -> #b:Type ->
  f:(a -> Tot b) ->
  s:Seq.seq a ->
  Tot (s':Seq.seq b{Seq.length s = Seq.length s' /\ 
    (forall (i:nat). {:pattern (Seq.index s' i)} i < Seq.length s' ==> Seq.index s' i == f (Seq.index s i))})
    (decreases (Seq.length s))
let rec seq_map #a #b f s =
  if Seq.length s = 0 then Seq.createEmpty
  else
    let s' = Seq.cons (f (Seq.head s)) (seq_map f (Seq.tail s)) in
    s'

val seq_map2:
  #a:Type -> #b:Type -> #c:Type ->
  f:(a -> b -> Tot c) ->
  s:Seq.seq a -> s':Seq.seq b{Seq.length s = Seq.length s'} ->
  Tot (s'':Seq.seq c{Seq.length s = Seq.length s'' /\
    (forall (i:nat). {:pattern (Seq.index s'' i)} i < Seq.length s'' ==> Seq.index s'' i == f (Seq.index s i) (Seq.index s' i))})
    (decreases (Seq.length s))
let rec seq_map2 #a #b #c f s s' =
  if Seq.length s = 0 then Seq.createEmpty
  else
    let s'' = Seq.cons (f (Seq.head s) (Seq.head s')) (seq_map2 f (Seq.tail s) (Seq.tail s')) in
    s''

(* JK: could that be interesting ? Needs to be adapted in a stateful combinator and proven *)
assume val seq_map_flatten:
  #a:Type -> #b:Type ->
  ratio:nat ->
  f:(a -> Tot (s:Seq.seq b{Seq.length s = ratio})) ->
  s:Seq.seq a ->
  Tot (s':Seq.seq b{ratio * Seq.length s = Seq.length s' /\
    (forall (i:nat). {:pattern (Seq.index s i) \/ (Seq.slice s' (ratio *i) (ratio*i+ratio))}
      (let _ = Math.Lemmas.distributivity_add_right ratio i 1 in
       i < Seq.length s ==> Seq.slice s' (ratio * i) ((ratio*i)+ratio) == f (Seq.index s i)))})
    (decreases (Seq.length s))


(* From Cédric's Chacha specification *)
val iter_: #a:Type -> n:nat -> (f: a -> Tot a) -> a -> Tot a (decreases n)
let rec iter_ #a n f x = if n = 0 then x else iter_ (n-1) f (f x)

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"

private
val lemma_iter: #a:Type -> n:nat{n > 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (iter_ n f x == f (iter_ (n-1) f x))
let rec lemma_iter #a n f x =
  if n = 1 then ()
  else lemma_iter (n-1) f (f x)

private
val lemma_iter_0: #a:Type -> n:nat{n = 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (iter_ n f x == x)
let rec lemma_iter_0 #a n f x = ()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

// A higher-order combinator that KreMLin is aware of and will extract as a
// proper for-loop
(* Jonathan's original for-loop proposal *)
(* val for: #(a: Type0) -> *)
(*   b:buffer a -> *)
(*   l:UInt32.t{ UInt32.( 0 <= v l /\ v l <= Buffer.length b) } -> *)
(*   start:UInt32.t{ UInt32.( 0 <= v start /\ v start <= v l )} -> *)
(*   inv:(HS.mem -> nat -> Type0) -> *)
(*   f:(i:UInt32.t{ UInt32.( v start <= v i /\ v i < v l ) } -> *)
(*     Stack unit *)
(*       (requires (fun h -> inv h (UInt32.v i))) *)
(*       (ensures (fun h_1 _ h_2 -> UInt32.(inv h_1 (v i) /\ inv h_2 (v i + 1))))) -> *)
(*   Stack unit *)
(*     (requires (fun h -> *)
(*       (forall (h: HS.mem) (i: nat). inv h i ==> live h b) /\ *)
(*       inv h (UInt32.v start))) *)
(*     (ensures (fun _ _ h_2 -> inv h_2 (UInt32.v l))) *)
(*     (decreases (UInt32.(v l - v start))) *)
(* let rec for #a b l start inv f = *)
(*   let open FStar.Buffer in *)
(*   if start = l then *)
(*     () *)
(*   else begin *)
(*     let x = b.(start) in *)
(*     f start; *)
(*     for b l (UInt32.(start +^ 1ul)) inv f *)
(*   end *)


(* Simplified version *)
val for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish >= UInt32.v start} ->
  inv:(HS.mem -> nat -> Type0) ->
  f:(i:UInt32.t{UInt32.(v start <= v i /\ v i < v finish)} -> Stack unit
                        (requires (fun h -> inv h (UInt32.v i)))
                        (ensures (fun h_1 _ h_2 -> UInt32.(inv h_1 (v i) /\ inv h_2 (v i + 1)))) ) ->
  Stack unit
    (requires (fun h -> inv h (UInt32.v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (UInt32.v finish)))
let rec for start finish inv f =
  let open FStar.Buffer in
  if start = finish then
    ()
  else begin
    f start;
    for (UInt32.(start +^ 1ul)) finish inv f
  end


val iter:
  #a:Type0 ->
  #len:nat ->
  #f:(s:Seq.seq a{Seq.length s = len} -> Tot (s':Seq.seq a{Seq.length s' = Seq.length s})) ->
  n:UInt32.t ->
  f':(b:buffer a{length b = len} -> Stack unit 
                     (requires (fun h -> live h b))
                     (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
                       /\ (let b0 = as_seq h0 b in
                          let b1 = as_seq h1 b in
                          b1 == f b0)))) ->
  b: buffer a ->
  l: UInt32.t{ UInt32.v l = Buffer.length b /\ UInt32.v l = len } ->
  Stack unit
    (requires (fun h -> live h b ))
    (ensures (fun h_1 r h_2 -> modifies_1 b h_1 h_2 /\ live h_1 b /\ live h_2 b
      /\ (let s = as_seq h_1 b in
         let s' = as_seq h_2 b in
         s' == iter_ (UInt32.v n) f s) ))
let iter #a #len #f max fc b l =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 b /\ modifies_1 b h0 h1 /\ i <= UInt32.v max
    /\ as_seq h1 b == iter_ i f (as_seq h0 b)
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v max ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    fc b;
    lemma_iter (UInt32.v i + 1) f (as_seq h0 b)
  in
  lemma_iter_0 0 f (as_seq h0 b);
  for 0ul max inv f'


val inplace_map:
  #a:Type0 ->
  f:(a -> Tot a) ->
  b: buffer a ->
  l: UInt32.t{ UInt32.v l = Buffer.length b } ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h_1 r h_2 -> modifies_1 b h_1 h_2 /\ live h_2 b /\ live h_1 b
      /\ (let s1 = as_seq h_1 b in
         let s2 = as_seq h_2 b in
         s2 == seq_map f s1) ))
let inplace_map #a f b l =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 b /\ modifies_1 b h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). {:pattern (get h1 b j)} (j >= i /\ j < UInt32.v l) ==> get h1 b j == get h0 b j)
    /\ (forall (j:nat). {:pattern (get h1 b j)} j < i ==> get h1 b j == f (get h0 b j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    b.(i) <- f (b.(i))
  in
  for 0ul l inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 b) (seq_map f (as_seq h0 b))


(* open FStar.Buffer.Quantifiers *)

val map:
  #a:Type0 -> #b:Type0 ->
  f:(a -> Tot b) ->
  output: buffer b ->
  input: buffer a{disjoint input output} ->
  l: UInt32.t{ UInt32.v l = Buffer.length output /\ UInt32.v l = Buffer.length input } ->
  Stack unit
    (requires (fun h -> live h input /\ live h output ))
    (ensures (fun h_1 r h_2 -> modifies_1 output h_1 h_2 /\ live h_2 input /\ live h_1 input /\ live h_2 output
      /\ live h_2 output
      /\ (let s1 = as_seq h_1 input in
         let s2 = as_seq h_2 output in
         s2 == seq_map f s1) ))
let map #a #b f output input l =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 output /\ live h1 input /\ modifies_1 output h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). {:pattern (get h1 output j)} (j >= i /\ j < UInt32.v l) ==> get h1 output j == get h0 output j)
    /\ (forall (j:nat). {:pattern (get h1 output j)} j < i ==> get h1 output j == f (get h0 input j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    output.(i) <- f (input.(i))
  in
  for 0ul l inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 output) (seq_map f (as_seq h0 input))


val inplace_map2:
  #a:Type0 -> #b:Type0 ->
  f:(a -> b -> Tot a) ->
  in1: buffer a ->
  in2: buffer b{disjoint in1 in2} ->
  l: UInt32.t{ UInt32.v l = Buffer.length in1 /\ UInt32.v l = Buffer.length in2} ->
  Stack unit
    (requires (fun h -> live h in1 /\ live h in2))
    (ensures (fun h_1 r h_2 -> modifies_1 in1 h_1 h_2 /\ live h_2 in1 /\ live h_2 in2
      /\ live h_1 in1 /\ live h_1 in2
      /\ (let s1 = as_seq h_1 in1 in
         let s2 = as_seq h_1 in2 in
         let s = as_seq h_2 in1 in
         s == seq_map2 f s1 s2) ))
let inplace_map2 #a #b f in1 in2 l =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 in1 /\ live h1 in2 /\ modifies_1 in1 h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). {:pattern (get h1 in1 j)} (j >= i /\ j < UInt32.v l) ==> get h1 in1 j == get h0 in1 j)
    /\ (forall (j:nat). {:pattern (get h1 in1 j)} j < i ==> get h1 in1 j == f (get h0 in1 j) (get h0 in2 j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    in1.(i) <- f (in1.(i)) (in2.(i))
  in
  for 0ul l inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 in1) (seq_map2 f (as_seq h0 in1) (as_seq h0 in2))


val map2:
  #a:Type0 -> #b:Type0 -> #c:Type0 ->
  f:(a -> b -> Tot c) ->
  output: buffer c ->
  in1: buffer a{disjoint output in1} -> in2: buffer b{disjoint output in2} ->
  l: UInt32.t{ UInt32.v l = Buffer.length output /\ UInt32.v l = Buffer.length in1
     /\ UInt32.v l = Buffer.length in2 } ->
  Stack unit
    (requires (fun h -> live h in1 /\ live h in2 /\ live h output ))
    (ensures (fun h_1 r h_2 -> modifies_1 output h_1 h_2 /\ live h_2 in1 /\ live h_2 in2
      /\ live h_1 in1 /\ live h_1 in2 /\ live h_2 output
      /\ (let s1 = as_seq h_1 in1 in
         let s2 = as_seq h_1 in2 in
         let s = as_seq h_2 output in
         s == seq_map2 f s1 s2) ))
let map2 #a #b #c f output in1 in2 l =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 output /\ live h1 in1 /\ live h1 in2 /\ modifies_1 output h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). {:pattern (get h1 output j)} (j >= i /\ j < UInt32.v l) ==> get h1 output j == get h0 output j)
    /\ (forall (j:nat). {:pattern (get h1 output j)} j < i ==> get h1 output j == f (get h0 in1 j) (get h0 in2 j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    output.(i) <- f (in1.(i)) (in2.(i))
  in
  for 0ul l inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 output) (seq_map2 f (as_seq h0 in1) (as_seq h0 in2))
