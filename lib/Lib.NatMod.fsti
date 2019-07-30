module Lib.NatMod

//val nat_mod: m:pos -> Type0
let nat_mod (m:pos) = n:nat{n < m}

val nat_mod_v: #m:pos -> x:nat_mod m -> n:nat{n < m /\ n == x}

val modulo: n:nat -> m:pos -> r:nat_mod m{nat_mod_v #m r == n % m}

val ( +% ) : #m:pos -> nat_mod m -> nat_mod m -> nat_mod m
val ( -% ) : #m:pos -> nat_mod m -> nat_mod m -> nat_mod m
val ( *% ) : #m:pos -> nat_mod m -> nat_mod m -> nat_mod m
val ( **% ) : #m:pos -> nat_mod m -> n:pos -> Tot (nat_mod m) (decreases n)
val ( =% ) : #m:pos -> nat_mod m -> nat_mod m -> bool
val ( <>% ) : #m:pos -> nat_mod m -> nat_mod m -> bool
