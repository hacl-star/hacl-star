
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
| _35_71 -> begin
(let bi = (Bigint.index_wide b (idx + ctr))
in (let cast = (UInt.wide_to_limb bi)
in (let _35_74 = ()
in (let _35_76 = ()
in (let _35_78 = (Bigint.upd_limb output (idx + ctr) cast)
in (let h1 = (FStar_ST.get ())
in (let _35_81 = ()
in (let _35_83 = ()
in (copy_to_bigint' output b idx len (ctr + 1))))))))))
end)))

let pow2_increases_lemma = (fun n m -> ())

let norm_bigint_lemma_1 = (fun h b -> ())

let copy_to_bigint = (fun output b -> (let h0 = (FStar_ST.get ())
in (let _35_119 = ()
in (let _35_121 = (copy_to_bigint' output b 0 Parameters.norm_length 0)
in (let h1 = (FStar_ST.get ())
in ())))))

let rec copy_to_bigint_wide' = (fun output b idx len ctr -> (let h0 = (FStar_ST.get ())
in (match ((len - ctr)) with
| 0 -> begin
()
end
| _35_161 -> begin
(let bi = (Bigint.index_limb b (idx + ctr))
in (let cast = (UInt.limb_to_wide bi)
in (let _35_164 = ()
in (let _35_166 = (Bigint.upd_wide output (idx + ctr) cast)
in (let h1 = (FStar_ST.get ())
in (let _35_169 = ()
in (let _35_171 = ()
in (copy_to_bigint_wide' output b idx len (ctr + 1)))))))))
end)))

let copy_to_bigint_wide = (fun output b -> (let h0 = (FStar_ST.get ())
in (let _35_185 = (copy_to_bigint_wide' output b 0 Parameters.norm_length 0)
in (let h1 = (FStar_ST.get ())
in ()))))

let copy_lemma = (fun h0 h1 sa a sb b -> ())

let rec erase = (fun b idx len ctr -> (let h0 = (FStar_ST.get ())
in (match ((len - ctr)) with
| 0 -> begin
()
end
| _35_239 -> begin
(let _35_240 = (Bigint.upd_limb b (idx + ctr) UInt.zero_limb)
in (let h1 = (FStar_ST.get ())
in (let _35_243 = ()
in (erase b idx len (ctr + 1)))))
end)))

let rec erase_wide = (fun b idx len ctr -> (let h0 = (FStar_ST.get ())
in (match ((len - ctr)) with
| 0 -> begin
()
end
| _35_264 -> begin
(let _35_265 = (Bigint.upd_wide b (idx + ctr) UInt.zero_wide)
in (let h1 = (FStar_ST.get ())
in (let _35_268 = ()
in (erase_wide b idx len (ctr + 1)))))
end)))

let standardized_eq_norm = (fun h size b -> ())

let modulo = (fun output b -> (let h0 = (FStar_ST.get ())
in (let _35_289 = (Modulo.freduce_degree b)
in (let _35_291 = (Modulo.freduce_coefficients b)
in (let h = (FStar_ST.get ())
in (let _35_294 = ()
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
in (let _35_396 = ()
in (let _35_398 = ()
in (let _35_400 = (Fsum.fsum' a b)
in (let h1 = (FStar_ST.get ())
in (let tmp = (Bigint.create_wide ((2 * Parameters.norm_length) - 1))
in (let h2 = (FStar_ST.get ())
in (let _35_405 = ()
in (let _35_407 = ()
in (let _35_409 = (copy_to_bigint_wide tmp a)
in (let h3 = (FStar_ST.get ())
in (let _35_412 = ()
in (let _35_414 = ()
in (let _35_416 = ()
in (let _35_418 = ()
in (let _35_420 = ()
in (let _35_422 = ()
in (let _35_424 = (modulo a tmp)
in (let h4 = (FStar_ST.get ())
in ()))))))))))))))))))))

let gfdifference_lemma = (fun h0 h1 res a b -> ())

let fdifference_lemma = (fun h0 h1 res a b -> ())

let lemma_helper_diff_0 = (fun h0 h1 a b -> ())

let lemma_helper_diff_1 = (Obj.magic ((fun a b p -> (FStar_All.failwith "Not yet implemented:lemma_helper_diff_1"))))

let fdifference = (fun a b -> (let h0 = (FStar_ST.get ())
in (let _35_482 = ()
in (let _35_484 = ()
in (let b' = (Bigint.create_limb Parameters.norm_length)
in (let _35_487 = (Bigint.blit_limb b b' Parameters.norm_length)
in (let h1 = (FStar_ST.get ())
in (let _35_490 = ()
in (let _35_492 = ()
in (let _35_494 = ()
in (let _35_496 = (Modulo.add_big_zero b')
in (let h2 = (FStar_ST.get ())
in (let _35_499 = ()
in (let _35_501 = ()
in (let _35_503 = ()
in (let _35_505 = ()
in (let _35_507 = (Fdifference.fdifference' a Parameters.ndiff' Parameters.ndiff b')
in (let h3 = (FStar_ST.get ())
in (let _35_510 = ()
in (let tmp = (Bigint.create_wide ((2 * Parameters.norm_length) - 1))
in (let h4 = (FStar_ST.get ())
in (let _35_514 = (copy_to_bigint_wide tmp a)
in (let h5 = (FStar_ST.get ())
in (let _35_517 = ()
in (let _35_519 = ()
in (let _35_521 = (modulo a tmp)
in (let h6 = (FStar_ST.get ())
in ())))))))))))))))))))))))))))

let fscalar = (fun res b n s -> (let h0 = (FStar_ST.get ())
in (let _35_548 = ()
in (let tmp = (Bigint.create_wide ((2 * Parameters.norm_length) - 1))
in (let _35_551 = (Fscalar.scalar' tmp b s)
in (let h = (FStar_ST.get ())
in (let _35_554 = ()
in (let _35_556 = (modulo res tmp)
in (let h1 = (FStar_ST.get ())
in ())))))))))

let norm_lemma_2 = (Obj.magic ((fun h b -> (FStar_All.failwith "Not yet implemented:norm_lemma_2"))))

let norm_lemma_3 = (fun h b -> ())

let gfmul_lemma = (fun h0 h1 res a b -> ())

let fmul_lemma = (fun h0 h1 res a b -> ())

let fmul = (fun res a b -> (let h0 = (FStar_ST.get ())
in (let _35_602 = ()
in (let _35_604 = ()
in (let tmp = (Bigint.create_wide ((2 * Parameters.norm_length) - 1))
in (let h1 = (FStar_ST.get ())
in (let _35_608 = ()
in (let _35_610 = ()
in (let _35_612 = ()
in (let _35_614 = ()
in (let _35_616 = ()
in (let _35_618 = ()
in (let _35_620 = (Fproduct.multiplication tmp a b)
in (let h2 = (FStar_ST.get ())
in (let _35_623 = ()
in (let _35_625 = (modulo res tmp)
in (let h3 = (FStar_ST.get ())
in ())))))))))))))))))

let fsquare = (fun res a -> (fmul res a a))




