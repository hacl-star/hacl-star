module Lib.Loops

open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes

val for_:
  start:size_t ->
  finish:size_t{v finish >= v start} ->
  inv:(mem -> nat  -> Type0) ->
  f:(i:size_t{v start <= v i /\ v i < v finish} -> Stack unit
                        (requires (fun h -> inv h (v i)))
                        (ensures (fun h_1 _ h_2 -> (inv h_1 (v i) /\ inv h_2 (v i + 1)))) ) ->
  Stack unit
    (requires (fun h -> inv h (v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (v finish)))
let rec for_ start finish inv f =
  if start =. finish then
    ()
  else begin
    f start;
    for_ (add_mod #SIZE start (size 1)) finish inv f
  end

let for = for_
