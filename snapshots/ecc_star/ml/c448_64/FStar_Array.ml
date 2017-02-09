
open Prims
type ' t array =
' t FStar_Seq.seq FStar_Heap.ref

let op_At_Bar = (fun _ _ -> (FStar_All.failwith "Not yet implemented:op_At_Bar"))

let of_seq = (fun s -> (FStar_All.failwith "Not yet implemented:of_seq"))

let to_seq = (fun s -> (FStar_All.failwith "Not yet implemented:to_seq"))

let create = (fun n init -> (FStar_All.failwith "Not yet implemented:create"))

let index = (fun x n -> (FStar_All.failwith "Not yet implemented:index"))

let upd = (fun x n v -> (FStar_All.failwith "Not yet implemented:upd"))

let length = (fun x -> (FStar_All.failwith "Not yet implemented:length"))

let op = (fun f x -> (FStar_All.failwith "Not yet implemented:op"))

let swap = (fun x i j -> (let h0 = (FStar_ST.get ())
in (let tmpi = (index x i)
in (let tmpj = (index x j)
in (let _11_65 = (upd x j tmpi)
in (let _11_67 = (upd x i tmpj)
in (let h1 = (FStar_ST.get ())
in ())))))))

let rec copy_aux = (fun s cpy ctr -> (match (((length cpy) - ctr)) with
| 0 -> begin
()
end
| _11_85 -> begin
(let _11_86 = (let _53_27 = (index s ctr)
in (upd cpy ctr _53_27))
in (copy_aux s cpy (ctr + 1)))
end))

let copy = (fun s -> (let cpy = (let _53_30 = (length s)
in (let _53_29 = (index s 0)
in (create _53_30 _53_29)))
in (let _11_96 = (copy_aux s cpy 0)
in cpy)))

let rec blit_aux = (fun s s_idx t t_idx len ctr -> (match ((len - ctr)) with
| 0 -> begin
()
end
| _11_120 -> begin
(let _11_121 = (let _53_37 = (index s (s_idx + ctr))
in (upd t (t_idx + ctr) _53_37))
in (blit_aux s s_idx t t_idx len (ctr + 1)))
end))

let rec blit = (fun s s_idx t t_idx len -> (blit_aux s s_idx t t_idx len 0))

let sub = (fun s idx len -> (let t = (let _53_46 = (index s 0)
in (create len _53_46))
in (let _11_152 = (blit s idx t 0 len)
in t)))




