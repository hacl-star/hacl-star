module Lib.LoopCombinators

let rec repeat_left lo hi a f acc =
  if lo = hi then acc
  else repeat_left (lo + 1) hi a f (f lo acc)

let rec repeat_right lo hi a f acc =
  if lo = hi then acc
  else f (hi - 1) (repeat_right lo (hi - 1) a f acc)

let rec repeat_right_plus lo mi hi a f acc =
  if hi = mi then ()
  else repeat_right_plus lo mi (hi - 1) a f acc

let rec repeat_left_right lo hi a f acc =
  if lo = hi then ()
  else
    begin
    repeat_right_plus lo (lo + 1) hi a f acc;
    repeat_left_right (lo + 1) hi a f (f lo acc)
    end

let repeat_gen n a f acc0 =
  repeat_right 0 n a f acc0

let unfold_repeat_gen n a f acc0 i = ()
(* // Proof when using [repeat_left]:
  repeat_left_right 0 (i + 1) a f acc0;
  repeat_left_right 0 i a f acc0
*)

let fixed_a (a:Type) (i:nat) = a

let repeati #a n f acc0 =
  repeat_gen n (fixed_a a) f acc0

let unfold_repeati #a n f acc0 i =
  unfold_repeat_gen n (fixed_a a) f acc0 i

let repeat #a n f acc0 =
  repeati n (fun i -> f) acc0

let repeat_range #a min max f x =
  repeat_left min max (fun _ -> a) f x

let rec repeat_range_inductive #a min max pred f x =
  repeat_left min max (fun i -> x:a{pred i x}) f x

let repeati_inductive #a =
  repeat_range_inductive #a 0
