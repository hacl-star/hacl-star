module Lib.LoopCombinators

let rec repeat_left lo hi a f acc =
  if lo = hi then acc
  else repeat_left (lo + 1) hi a f (f lo acc)

let rec repeat_left_all_ml lo hi a f acc =
  if lo = hi then acc
  else repeat_left_all_ml (lo + 1) hi a f (f lo acc)

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
let fixed_i f (i:nat) = f

let repeati #a n f acc0 =
  repeat_gen n (fixed_a a) f acc0

let unfold_repeati #a n f acc0 i =
  unfold_repeat_gen n (fixed_a a) f acc0 i

let eq_repeati0 #a n f acc0 = ()

let repeat #a n f acc0 =
  repeati n (fixed_i f) acc0

let eq_repeat0 #a f acc0 = ()

let unfold_repeat #a n f acc0 i =
  unfold_repeati #a n (fixed_i f) acc0 i

let repeat_range #a min max f x =
  repeat_left min max (fun _ -> a) f x

let repeat_range_all_ml #a min max f x =
  repeat_left_all_ml min max (fun _ -> a) f x

let repeat_range_inductive #a min max pred f x =
  repeat_left min max (fun i -> x:a{pred i x}) f x

let repeati_inductive #a n pred f x0 =
  repeat_range_inductive #a 0 n pred f x0

let repeati_inductive_repeat_gen #a n pred f x0 =
  let a' i = x:a{pred i x} in
  let f' (i:nat{i < n}) (x:a' i) : y:a' (i + 1) = f i x in
  repeat_left_right 0 n (fun i -> x:a{pred i x}) f x0;
  assert_norm (repeati_inductive n pred f x0 == repeat_right 0 n (fun i -> a' i) f' x0);
  assert (repeat_gen n (fun i -> x:a{pred i x}) f x0 == repeat_right 0 n a' f' x0);
  let repeat_right_eta
    (a:(i:nat{0 <= i /\ i <= n} -> Type))
    (f:(i:nat{0 <= i /\ i < n} -> a i -> a (i + 1)))
    (acc:a 0) :
    Lemma (repeat_right 0 n a f acc == repeat_right 0 n (fun i -> a i) f acc) = () in
  repeat_right_eta a' f' x0

let repeat_gen_inductive n a pred f x0 =
  let f' (i:nat{i < n})
         (x:a i{pred i x /\ x == repeat_gen i a f x0})
         : x':a (i + 1){pred (i + 1) x' /\ x' == repeat_gen (i + 1) a f x0}
         = f i x in
  repeat_gen n (fun i -> x:a i{pred i x /\ x == repeat_gen i a f x0}) f' x0

let repeati_inductive' #a n pred f x0 =
  let f'
    (i:nat{i < n})
    (x:a{pred i x /\ x == repeati i f x0})
    : x':a{pred (i + 1) x' /\ x' == repeati (i + 1) f x0}
    = f i x in
  repeat_gen n (fun i -> x:a{pred i x /\ x == repeati i f x0}) f' x0
