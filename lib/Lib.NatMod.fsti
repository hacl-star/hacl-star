module Lib.NatMod

val nat_mod: m:pos -> Type0

val nat_mod_v: #m:pos -> nat_mod m -> n:nat{n < m}

val modulo: n:nat -> m:pos -> r:nat_mod m{nat_mod_v #m r == n % m}

val ( +% ) : #m:pos -> nat_mod m -> nat_mod m -> nat_mod m
val ( -% ) : #m:pos -> nat_mod m -> nat_mod m -> nat_mod m
val ( *% ) : #m:pos -> nat_mod m -> nat_mod m -> nat_mod m
val ( **% ) : #m:pos -> nat_mod m -> pos -> nat_mod m

