module Lib.Loops

open Lib.IntTypes

let for start finish inv f =
  C.Loops.for
    start
    finish
    (fun h i -> v start <= i /\ i <= v finish /\ inv h i)
    (fun i -> f i)

let while inv guard test body =
  let test: unit -> Stack bool
    (requires inv)
    (ensures  fun _ b h -> inv h /\ b == guard h)
  = test
  in
  C.Loops.while #inv #(fun b h -> inv h /\ b == guard h) test body

/// Test

#set-options "--max_fuel 3 --max_ifuel 0 --z3rlimit 50"

val square_while: unit -> Stack UInt32.t (fun _ -> true) (fun h0 x h1 -> x == 9ul)
let square_while () =
  let open LowStar.Buffer in
  let open LowStar.BufferOps in
  let open FStar.UInt32 in
  push_frame();
  let l = [ 1ul; 2ul; 3ul ] in
  let b = alloca_of_list l in
  let r = alloca 0ul 1ul in
  let h = HyperStack.ST.get() in
  assert (forall i. Seq.index (Seq.seq_of_list l) i == List.Tot.index l i);
  let h0 = HyperStack.ST.get () in
  let inv h = live h b /\ live h r /\
    get h r 0 <=^ 3ul /\
    (forall (i:nat{i < 3}). i < v (get h r 0) ==> get h b i == get h0 b i *^ get h0 b i) /\
    (forall (i:nat{i < 3}). v (get h r 0) <= i ==> get h b i == get h0 b i)
  in
  let guard h = get h r 0 <^ 3ul in
  while inv guard (fun () -> !*r <^ 3ul) (fun () ->
    b.(!*r) <- b.(!*r) *^ b.(!*r);
    r.(0ul) <- !*r +^ 1ul
  );
  let x = b.(2ul) in
  pop_frame();
  x
