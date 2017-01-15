
let rec pow2 n =
  match n with
  | 0 -> 1 | _ -> 2 * pow2 (n-1)

let log_2 (n:int) =
  int_of_float (Pervasives.log (float_of_int n))
