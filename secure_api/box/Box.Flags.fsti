module Box.Flags

val model: b:bool

val prf_odh : b:bool{b ==> model}

val ae: b:bool{b ==> model /\ prf_odh}

val pkae : b:bool{(b <==> (prf_odh /\ ae)) /\ (b ==> model)}
