
open Prims
let constant_template_lemma = (fun size_a a size_b b -> ())

let rec bitweight_lemma_1 = (fun t i -> ())

let rec bitweight_lemma_0 = (fun t i j -> ())

let auxiliary_lemma_1 = (fun t a b -> ())

let gmultiplication_step_lemma_1 = (fun h0 h1 a b c idx len -> ())

let multiplication_step_lemma_1 = (fun h0 h1 a b c idx len -> ())

let gmultiplication_step_lemma_2 = (fun h0 h1 a b c idx len -> ())

let multiplication_step_lemma_2 = (fun h0 h1 a b c idx len -> ())

let rec multiplication_step_lemma = (fun h0 h1 a b c idx len -> ())

let max_limb = (let _34_261 = ()
in (((Parameters.platform_wide - (IntLib.log_2 Parameters.norm_length)) - 1) / 2))

let max_wide = (2 * max_limb)

let auxiliary_lemma_2 = (fun h0 h1 h2 a b ctr c -> ())

let auxiliary_lemma_3 = (fun h0 h1 h2 a b ctr c -> ())

let rec gauxiliary_lemma_5 = (fun h0 h1 size_a a size_b b c len len2 -> ())

let auxiliary_lemma_5 = (fun h0 h1 size_a a size_b b c len len2 -> ())

let max_limb_lemma = (fun a b -> ())

let gmax_limb_lemma2 = (fun h a b i ctr -> ())

let max_limb_lemma2 = (fun h a b i ctr -> ())

let is_scalar_product_lemma = (fun h0 h1 a s res -> ())

let multiplication_step_0 = (fun a b ctr c tmp -> (let h0 = (FStar_ST.get ())
in (let s = (Bigint.index_limb b ctr)
in (let _34_493 = ()
in (let _34_496 = ()
in (let _34_498 = ()
in (let _34_501 = ()
in (let _34_503 = ()
in (let _34_506 = ()
in (let _34_508 = (Fscalar.scalar_multiplication_tr tmp a s 0)
in (let h1 = (FStar_ST.get ())
in ())))))))))))

let std_lemma = (fun h0 h1 a tmp -> ())

let max_wide_lemma = (Obj.magic ((fun x -> (FStar_All.failwith "Not yet implemented:max_wide_lemma"))))

let lemma_helper_00 = (fun _34_546 -> ())

let lemma_helper_01 = (fun a b c -> ())

let lemma_helper_02 = (fun a b c -> ())

let multiplication_step_lemma_0010 = (fun h0 h1 a b ctr c tmp -> ())

let multiplication_step_lemma_001 = (fun h0 h1 a b ctr c tmp -> ())

let multiplication_step_lemma_01 = (fun h0 h1 a b ctr c tmp -> ())

let partial_equality_lemma = (fun h0 h1 c ctr -> ())

let lemma_helper_10 = (fun a b c -> ())

let max_value_lemma_1 = (fun h0 h1 h2 a b ctr c tmp -> ())

let max_value_lemma = (fun h0 h1 h2 a b ctr c tmp -> ())

let standardized_lemma = (fun h0 h1 h2 a c tmp -> ())

let length_lemma = (fun h0 h1 h2 c ctr tmp -> ())

let lemma_helper_20 = (fun h0 h1 h2 a b ctr c tmp -> ())

let multiplication_step_lemma_02 = (fun h0 h1 h2 a b ctr c tmp -> ())

let multiplication_step_p1 = (fun a b ctr c tmp -> (let h0 = (FStar_ST.get ())
in (let _34_975 = (multiplication_step_0 a b ctr c tmp)
in (let h1 = (FStar_ST.get ())
in (let _34_978 = ()
in (let _34_980 = (FsumWide.fsum_index c ctr tmp 0 Parameters.norm_length 0)
in (let h2 = (FStar_ST.get ())
in ())))))))

let ghelper_lemma_6 = (fun h0 h1 a b ctr c tmp -> ())

let helper_lemma_6 = (fun h0 h1 a b ctr c tmp -> ())

let multiplication_step = (fun a b ctr c tmp -> (let h0 = (FStar_ST.get ())
in (let _34_1043 = (multiplication_step_p1 a b ctr c tmp)
in (let h1 = (FStar_ST.get ())
in ()))))

let gmultiplication_step_lemma_03 = (fun h0 h1 a b ctr c -> ())

let multiplication_step_lemma_03 = (fun h0 h1 a b ctr c -> ())

let helper_lemma_7 = (fun ctr -> ())

let gmultiplication_aux_lemma = (fun h0 h1 a b ctr c tmp -> ())

let multiplication_aux_lemma = (fun h0 h1 a b ctr c tmp -> ())

let multiplication_aux_lemma_2 = (fun h0 h1 h2 a b ctr c tmp -> ())

let rec multiplication_aux = (fun a b ctr c tmp -> (let h0 = (FStar_ST.get ())
in (match (ctr) with
| 0 -> begin
()
end
| _34_1219 -> begin
(let _34_1220 = ()
in (let _34_1222 = (multiplication_step a b (Parameters.norm_length - ctr) c tmp)
in (let h1 = (FStar_ST.get ())
in (let _34_1225 = ()
in (let _34_1227 = (multiplication_aux a b (ctr - 1) c tmp)
in (let h2 = (FStar_ST.get ())
in ()))))))
end)))

let helper_lemma_16 = (fun h0 h1 a mods -> ())

let helper_lemma_13 = (fun h0 h1 a -> ())

let helper_lemma_15 = (fun h0 h1 c -> ())

let gmultiplication_lemma_1 = (fun h0 h1 c a b -> ())

let multiplication_lemma_1 = (fun h0 h1 c a b -> ())

let helper_lemma_14 = (fun h0 h1 h2 c tmp -> ())

let multiplication_lemma_2 = (fun h0 h1 h2 c a b tmp -> ())

let multiplication = (fun c a b -> (let h0 = (FStar_ST.get ())
in (let tmp = (Bigint.create_wide Parameters.norm_length)
in (let h1 = (FStar_ST.get ())
in (let _34_1351 = ()
in (let _34_1353 = ()
in (let _34_1355 = ()
in (let _34_1357 = ()
in (let _34_1359 = (multiplication_aux a b Parameters.norm_length c tmp)
in (let h2 = (FStar_ST.get ())
in ()))))))))))




