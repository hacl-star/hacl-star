
open Prims
let nat_to_felem = (Obj.magic ((fun x -> (FStar_All.failwith "Not yet implemented:nat_to_felem"))))

let felem_to_nat = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:felem_to_nat"))))

let finite_field_implementation = (Obj.magic ((fun x -> (FStar_All.failwith "Not yet implemented:finite_field_implementation"))))

let felem_lemma = (Obj.magic ((fun x y -> (FStar_All.failwith "Not yet implemented:felem_lemma"))))

let valueOf = (Obj.magic ((fun h size b -> (FStar_All.failwith "Not yet implemented:valueOf"))))

let valueOfBytes = (fun h b -> (Obj.magic (())))

let gcast_lemma_1 = (fun x -> ())

let cast_lemma_1 = (fun x -> ())

let rec copy_to_bigint' = (fun output b idx len ctr -> (let h0 = (FStar_ST.get ())
in (match ((len - ctr)) with
| 0 -> begin
()
end
| _36_71 -> begin
(let bi = (Bigint.index_wide b (idx + ctr))
in (let cast = (UInt.wide_to_limb bi)
in (let _36_74 = ()
in (let _36_76 = ()
in (let _36_78 = (Bigint.upd_limb output (idx + ctr) cast)
in (let h1 = (FStar_ST.get ())
in (let _36_81 = ()
in (let _36_83 = ()
in (copy_to_bigint' output b idx len (ctr + 1))))))))))
end)))

let pow2_increases_lemma = (fun n m -> ())

let norm_bigint_lemma_1 = (fun h b -> ())

let copy_to_bigint = (fun output b -> (let h0 = (FStar_ST.get ())
in (let _36_119 = ()
in (let _36_121 = (copy_to_bigint' output b 0 Parameters.norm_length 0)
in (let h1 = (FStar_ST.get ())
in ())))))

let rec copy_to_bigint_wide' = (fun output b idx len ctr -> (let h0 = (FStar_ST.get ())
in (match ((len - ctr)) with
| 0 -> begin
()
end
| _36_161 -> begin
(let bi = (Bigint.index_limb b (idx + ctr))
in (let cast = (UInt.limb_to_wide bi)
in (let _36_164 = ()
in (let _36_166 = (Bigint.upd_wide output (idx + ctr) cast)
in (let h1 = (FStar_ST.get ())
in (let _36_169 = ()
in (let _36_171 = ()
in (copy_to_bigint_wide' output b idx len (ctr + 1)))))))))
end)))

let copy_to_bigint_wide = (fun output b -> (let h0 = (FStar_ST.get ())
in (let _36_185 = (copy_to_bigint_wide' output b 0 Parameters.norm_length 0)
in (let h1 = (FStar_ST.get ())
in ()))))

let copy_lemma = (fun h0 h1 sa a sb b -> ())

let rec erase = (fun b idx len ctr -> (let h0 = (FStar_ST.get ())
in (match ((len - ctr)) with
| 0 -> begin
()
end
| _36_239 -> begin
(let _36_240 = (Bigint.upd_limb b (idx + ctr) UInt.zero_limb)
in (let h1 = (FStar_ST.get ())
in (let _36_243 = ()
in (erase b idx len (ctr + 1)))))
end)))

let rec erase_wide = (fun b idx len ctr -> (let h0 = (FStar_ST.get ())
in (match ((len - ctr)) with
| 0 -> begin
()
end
| _36_264 -> begin
(let _36_265 = (Bigint.upd_wide b (idx + ctr) UInt.zero_wide)
in (let h1 = (FStar_ST.get ())
in (let _36_268 = ()
in (erase_wide b idx len (ctr + 1)))))
end)))

let standardized_eq_norm = (fun h size b -> ())

let modulo = (fun output b -> (let h0 = (FStar_ST.get ())
in (let _36_289 = (Modulo.freduce_degree b)
in (let _36_291 = (Modulo.freduce_coefficients b)
in (let h = (FStar_ST.get ())
in (let _36_294 = ()
in (copy_to_bigint output b)))))))

let gfsum_lemma = (fun h0 h1 res a b -> ())

let fsum_lemma = (fun h0 h1 res a b -> ())

let lemma_helper_sum_0 = (fun h0 h1 a b -> ())

let lemma_helper_sum_1 = (fun h0 h1 a b -> ())

let lemma_helper_fsum_3 = (fun a b -> ())

let rec glemma_helper_fsum_2 = (fun h tmp len -> ())

let lemma_helper_fsum_2 = (fun h tmp len -> ())

let lemma_fsum_1 = (fun h1 h2 a -> ())

let fsum = (fun a b -> (let h0 = (FStar_ST.get ())
in (let _36_396 = ()
in (let _36_398 = ()
in (let _36_400 = (Fsum.fsum' a b)
in (let h1 = (FStar_ST.get ())
in (let tmp = (Bigint.create_wide ((2 * Parameters.norm_length) - 1))
in (let h2 = (FStar_ST.get ())
in (let _36_405 = ()
in (let _36_407 = ()
in (let _36_409 = (copy_to_bigint_wide tmp a)
in (let h3 = (FStar_ST.get ())
in (let _36_412 = ()
in (let _36_414 = ()
in (let _36_416 = ()
in (let _36_418 = ()
in (let _36_420 = ()
in (let _36_422 = ()
in (let _36_424 = (modulo a tmp)
in (let h4 = (FStar_ST.get ())
in ()))))))))))))))))))))

let gfdifference_lemma = (fun h0 h1 res a b -> ())

let fdifference_lemma = (fun h0 h1 res a b -> ())

let lemma_helper_diff_0 = (fun h0 h1 a b -> ())

let lemma_helper_diff_1 = (Obj.magic ((fun a b p -> (FStar_All.failwith "Not yet implemented:lemma_helper_diff_1"))))

let fdifference = (fun a b -> (let h0 = (FStar_ST.get ())
in (let _36_482 = ()
in (let _36_484 = ()
in (let b' = (Bigint.create_limb Parameters.norm_length)
in (let _36_487 = (Bigint.blit_limb b b' Parameters.norm_length)
in (let h1 = (FStar_ST.get ())
in (let _36_490 = ()
in (let _36_492 = ()
in (let _36_494 = ()
in (let _36_496 = (Modulo.add_big_zero b')
in (let h2 = (FStar_ST.get ())
in (let _36_499 = ()
in (let _36_501 = ()
in (let _36_503 = ()
in (let _36_505 = ()
in (let _36_507 = (Fdifference.fdifference' a Parameters.ndiff' Parameters.ndiff b')
in (let h3 = (FStar_ST.get ())
in (let _36_510 = ()
in (let tmp = (Bigint.create_wide ((2 * Parameters.norm_length) - 1))
in (let h4 = (FStar_ST.get ())
in (let _36_514 = (copy_to_bigint_wide tmp a)
in (let h5 = (FStar_ST.get ())
in (let _36_517 = ()
in (let _36_519 = ()
in (let _36_521 = (modulo a tmp)
in (let h6 = (FStar_ST.get ())
in ())))))))))))))))))))))))))))

let fscalar = (fun res b n s -> (let h0 = (FStar_ST.get ())
in (let _36_548 = ()
in (let tmp = (Bigint.create_wide ((2 * Parameters.norm_length) - 1))
in (let _36_551 = (Fscalar.scalar' tmp b s)
in (let h = (FStar_ST.get ())
in (let _36_554 = ()
in (let _36_556 = (modulo res tmp)
in (let h1 = (FStar_ST.get ())
in ())))))))))

let norm_lemma_2 = (Obj.magic ((fun h b -> (FStar_All.failwith "Not yet implemented:norm_lemma_2"))))

let norm_lemma_3 = (fun h b -> ())

let gfmul_lemma = (fun h0 h1 res a b -> ())

let fmul_lemma = (fun h0 h1 res a b -> ())

let fmul = (fun res a b -> (let h0 = (FStar_ST.get ())
in (let _36_602 = ()
in (let _36_604 = ()
in (let tmp = (Bigint.create_wide ((2 * Parameters.norm_length) - 1))
in (let h1 = (FStar_ST.get ())
in (let _36_608 = ()
in (let _36_610 = ()
in (let _36_612 = ()
in (let _36_614 = ()
in (let _36_616 = ()
in (let _36_618 = ()
in (let _36_620 = (Fproduct.multiplication tmp a b)
in (let h2 = (FStar_ST.get ())
in (let _36_623 = ()
in (let _36_625 = (modulo res tmp)
in (let h3 = (FStar_ST.get ())
in ())))))))))))))))))

let fsquare = (fun res a -> (fmul res a a))




