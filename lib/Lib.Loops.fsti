module Lib.Loops

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes

inline_for_extraction
val for:
    start:size_t
  -> finish:size_t{v finish >= v start}
  -> inv:(mem -> (i:nat{v start <= i /\ i <= v finish}) -> Type0)
  -> f:(i:size_t{v start <= v i /\ v i < v finish} -> Stack unit
                  (requires fun h -> inv h (v i))
                  (ensures  fun h_1 _ h_2 -> inv h_2 (v i + 1))) ->
  Stack unit
    (requires fun h -> inv h (v start))
    (ensures  fun _ _ h_2 -> inv h_2 (v finish))

(*
{inv h0}
while (test ()) do
  {inv h1 /\ guard h1}
  body ()
  {inv h2}
{~(guard h3) /\ inv h3}
*)
inline_for_extraction
val while:
    inv: (mem -> Type0)
  -> guard: (h:mem{inv h} -> GTot bool)
  -> test: (unit -> Stack bool 
                    (requires inv) 
                    (ensures  fun h0 b h1 -> b == guard h0 /\ h0 == h1))
  -> body: (unit -> Stack unit
                    (requires fun h -> inv h /\ guard h)
                    (ensures  fun _ _ h -> inv h))
  -> Stack unit
      (requires inv)
      (ensures  fun _ _ h -> inv h /\ ~(guard h))
