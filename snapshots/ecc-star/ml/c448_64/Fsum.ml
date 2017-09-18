
open Prims
let fsum_index_aux = (fun a b ctr -> (let h0 = (FStar_ST.get ())
in (let ai = (Bigint.index_limb a ctr)
in (let bi = (Bigint.index_limb b ctr)
in (let _27_30 = ()
in (let _27_32 = ()
in (let z = (UInt.add_limb ai bi)
in (let _27_35 = (Bigint.upd_limb a ctr z)
in (let h1 = (FStar_ST.get ())
in ())))))))))

let fsum_index_lemma = (fun h0 h1 h2 a b ctr -> ())

let rec fsum_index = (fun a b ctr -> (let h0 = (FStar_ST.get ())
in (match ((Parameters.norm_length - ctr)) with
| 0 -> begin
()
end
| _27_107 -> begin
(let _27_108 = (fsum_index_aux a b ctr)
in (let h1 = (FStar_ST.get ())
in (let _27_111 = ()
in (let _27_113 = ()
in (let _27_115 = (fsum_index a b (ctr + 1))
in (let h2 = (FStar_ST.get ())
in ()))))))
end)))

let gaddition_lemma_aux = (fun h0 h1 a b len -> ())

let addition_lemma_aux = (fun h0 h1 a b len -> ())

let rec addition_lemma = (fun h0 h1 a b len -> ())

let addition_max_value_lemma = (fun h0 h1 a b c -> ())

let max_value_lemma = (fun h a m -> ())

let addition_max_value_lemma_extended = (fun h0 h1 a b c idx len -> ())

let gauxiliary_lemma_2 = (fun ha a hb b i -> ())

let auxiliary_lemma_2 = (fun ha a hb b i -> ())

let auxiliary_lemma_0 = (fun ha a hb b -> ())

let auxiliary_lemma_1 = (fun h0 h1 b -> ())

let auxiliary_lemma_3 = (fun h0 h1 a b -> ())

let fsum' = (fun a b -> (let h0 = (FStar_ST.get ())
in (let _27_336 = ()
in (let _27_338 = (fsum_index a b 0)
in (let h1 = (FStar_ST.get ())
in ())))))




