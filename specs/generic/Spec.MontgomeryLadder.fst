module Spec.MontgomeryLadder


#set-options "--initial_fuel 0 --max_fuel 0"

type additive_law (a:eqtype) (zero:a) = add:(x:a -> y:a -> Tot a)
  {forall x y z. x `add` y = y `add` x /\ (x `add` y) `add` z = x `add` (y `add` z) /\ x `add` zero = x}

let rec exp #a #zero (add:additive_law a zero) x (k:nat) =
  if k = 0 then zero
  else x `add` (exp add x (k-1))

let cswap swap x y = if swap then y,x else x,y

val montgomery_ladder_:
  #a:eqtype -> #zero:a ->
  f:additive_law a zero ->
  init:a ->
  x:a ->
  xp1:a ->
  k:nat ->
  ctr:nat(* {x = exp f init (k / pow2 ctr) /\ xp1 = exp f init (k / pow2 ctr + 1)} *) ->
  max:nat{ctr <= max /\ k < pow2 max} ->
  Tot (y:a(* {y = exp f init k} *))
      (decreases ctr)
let rec montgomery_ladder_ #a #zero plus init x xp1 k ctr max =
  if ctr = 0 then x
  else (
    let ctr = ctr - 1 in
    let swap = k / pow2 ctr % 2 = 1 in
    let x, xp1 =
      if swap then x `plus` xp1, xp1 `plus` xp1
      else x `plus` x, x `plus` xp1 in
    montgomery_ladder_ plus init x xp1 k ctr max
  )
        



(* val montgomery_ladder: k:scalar -> u:serialized_point -> Tot elem *)
(* let montgomery_ladder k u = *)
(*   let rec loop k x_1 x_2 z_2 x_3 z_3 swap (ctr:nat) : Tot (tuple5 elem elem elem elem bool) *)
(*                                                    (decreases (ctr)) *)
(*   = *)
(*     if ctr = 0 then (x_2, z_2, x_3, z_3, swap) *)
(*     else ( *)
(*       let ctr = ctr - 1 in *)
(*       let k_t = (k / pow2 ctr) % 2 = 1 in // ctr-th bit of the scalar *)
(*       let swap = swap `xor` k_t in *)
(*       let x_2, x_3 = cswap swap x_2 x_3 in *)
(*       let z_2, z_3 = cswap swap z_2 z_3 in *)
(*       let swap = k_t in *)
(*       let x_2, z_2 ,x_3, z_3 = add_and_double x_1 x_2 z_2 x_3 z_3 in *)
(*       loop k x_1 x_2 z_2 x_3 z_3 swap ctr *)
(*   ) in *)

