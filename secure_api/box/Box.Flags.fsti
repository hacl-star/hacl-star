module Box.Flags

val prf_odh : b:bool

val ae: b:bool{b ==> prf_odh}

val pkae : b:bool{b <==> prf_odh /\ ae}
