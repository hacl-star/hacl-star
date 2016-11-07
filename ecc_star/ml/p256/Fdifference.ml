
open Prims
let helper_lemma_1 = (fun i len v -> ())

let fdifference_aux_1 = (fun a b ctr -> (let h0 = (FStar_ST.get ())
in (let i = ctr
in (let _29_25 = ()
in (let _29_27 = ()
in (let _29_29 = ()
in (let ai = (Bigint.index_limb a i)
in (let bi = (Bigint.index_limb b i)
in (let _29_33 = ()
in (let _29_35 = ()
in (let z = (UInt.sub_limb bi ai)
in (let _29_38 = (Bigint.upd_limb a i z)
in (let h1 = (FStar_ST.get ())
in ())))))))))))))

let fdifference_aux_2_0 = (fun h0 h1 h2 a b ctr -> ())

let fdifference_aux_2_1 = (fun h0 h1 h2 a b ctr -> ())

let fdifference_aux_2 = (fun h0 h1 h2 a b ctr -> ())

let rec fdifference_aux = (fun a b ctr -> (let h0 = (FStar_ST.get ())
in (match ((Parameters.norm_length - ctr)) with
| 0 -> begin
()
end
| _29_136 -> begin
(let _29_137 = (fdifference_aux_1 a b ctr)
in (let h1 = (FStar_ST.get ())
in (let _29_140 = ()
in (let _29_142 = (fdifference_aux a b (ctr + 1))
in (let h2 = (FStar_ST.get ())
in ())))))
end)))

let gsubtraction_lemma_aux = (fun h0 h1 a b len -> ())

let subtraction_lemma_aux = (fun h0 h1 a b len -> ())

let rec subtraction_lemma = (fun h0 h1 a b len -> ())

let subtraction_max_value_lemma = (fun h0 h1 a b c -> ())

let max_value_lemma = (fun h a m -> ())

let subtraction_max_value_lemma_extended = (fun h0 h1 a b c -> ())

let gauxiliary_lemma_2 = (fun ha a min max hb b i -> ())

let auxiliary_lemma_2 = (fun ha a min max hb b i -> ())

let auxiliary_lemma_0 = (fun ha a min max hb b -> ())

let auxiliary_lemma_1 = (fun h0 h1 mods min max b -> ())

let fdifference' = (fun a min max b -> (let h0 = (FStar_ST.get ())
in (let _29_373 = ()
in (let _29_375 = (fdifference_aux a b 0)
in (let h1 = (FStar_ST.get ())
in ())))))




