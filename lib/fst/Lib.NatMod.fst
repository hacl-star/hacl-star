module Lib.NatMod

//let nat_mod (m:pos) = n:nat {n < m}

let nat_mod_v (#m:pos) n = n

let modulo (n:nat) (m:pos) = n % m

let ( +% ) (#m:pos) n1 n2 = (n1 + n2) % m
let ( -% ) (#m:pos) n1 n2 = (n1 + m - n2) % m
let ( *% ) (#m:pos) n1 n2 = (n1 `op_Multiply` n2) % m

let rec ( **% ) #m e n =
  if n = 1 then e
  else
    if n % 2 = 0 then (e *% e) **% (n / 2)
    else e *% ((e *% e) **% ((n-1)/2))

let ( =% ) (#m:pos) n1 n2 = n1 = n2
let ( <>% ) (#m:pos) n1 n2 = n1 <> n2
