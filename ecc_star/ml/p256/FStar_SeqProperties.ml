
open Prims
let lemma_append_inj_l = (fun s1 s2 t1 t2 i -> ())

let lemma_append_inj_r = (fun s1 s2 t1 t2 i -> ())

let lemma_append_len_disj = (fun s1 s2 t1 t2 -> ())

let lemma_append_inj = (fun s1 s2 t1 t2 -> ())

let head = (fun s -> (FStar_Seq.index s 0))

let tail = (fun s -> (FStar_Seq.slice s 1 (FStar_Seq.length s)))

let cons = (fun x s -> (FStar_Seq.append (FStar_Seq.create 1 x) s))

let split = (fun s i -> ((FStar_Seq.slice s 0 i), (FStar_Seq.slice s i (FStar_Seq.length s))))

let lemma_split = (fun s i -> ())

let split_eq = (fun s i -> (let x = (split s i)
in (let _7_88 = ()
in x)))

let rec count = (fun x s -> if ((FStar_Seq.length s) = 0) then begin
0
end else begin
if ((head s) = x) then begin
(1 + (count x (tail s)))
end else begin
(count x (tail s))
end
end)

let mem = (fun x l -> ((count x l) > 0))

let swap = (fun s i j -> (FStar_Seq.upd (FStar_Seq.upd s j (FStar_Seq.index s i)) i (FStar_Seq.index s j)))

let lemma_slice_append = (fun s1 s2 -> ())

let rec lemma_append_cons = (fun s1 s2 -> ())

let lemma_tl = (fun hd tl -> ())

let rec sorted = (fun f s -> if ((FStar_Seq.length s) <= 1) then begin
true
end else begin
(let hd = (head s)
in ((f hd (FStar_Seq.index s 1)) && (sorted f (tail s))))
end)

let rec lemma_append_count = (fun lo hi -> ())

let lemma_append_count_aux = (fun x lo hi -> ())

let lemma_mem_inversion = (fun s -> ())

let rec lemma_mem_count = (fun s f -> ())

let lemma_count_slice = (fun s i -> ())

type ' a tot_ord =
' a  ->  ' a  ->  Prims.bool

let rec sorted_concat_lemma = (fun f lo pivot hi -> ())

let split_5 = (fun s i j -> (Prims.admit ()))

let lemma_swap_permutes_aux_frag_eq = (fun s i j i' j' -> ())

let lemma_swap_permutes_aux = (fun s i j x -> ())

let lemma_swap_permutes = (fun s i j -> ())

let cons_perm = (fun tl s -> ())

let lemma_mem_append = (fun s1 s2 -> ())

let lemma_slice_cons = (fun s i j -> ())

let lemma_slice_snoc = (fun s i j -> ())

let lemma_ordering_lo_snoc = (fun f s i j pv -> ())

let lemma_ordering_hi_cons = (fun f s back len pv -> ())

let swap_frame_lo = (fun s lo i j -> ())

let swap_frame_lo' = (fun s lo i' i j -> ())

let swap_frame_hi = (fun s i j k hi -> ())

let lemma_swap_slice_commute = (fun s start i j len -> ())

let lemma_swap_permutes_slice = (fun s start i j len -> ())

let splice = (fun s1 i s2 j -> (FStar_Seq.append (FStar_Seq.slice s1 0 i) (FStar_Seq.append (FStar_Seq.slice s2 i j) (FStar_Seq.slice s1 j (FStar_Seq.length s1)))))

let splice_refl = (fun s i j -> ())

let lemma_swap_splice = (fun s start i j len -> ())

let lemma_seq_frame_hi = (fun s1 s2 i j m n -> ())

let lemma_seq_frame_lo = (fun s1 s2 i j m n -> ())

let lemma_tail_slice = (fun s i j -> ())

let lemma_weaken_frame_right = (fun s1 s2 i j k -> ())

let lemma_weaken_frame_left = (fun s1 s2 i j k -> ())

let lemma_trans_frame = (fun s1 s2 s3 i j -> ())

let lemma_weaken_perm_left = (fun s1 s2 i j k -> ())

let lemma_weaken_perm_right = (fun s1 s2 i j k -> ())

let lemma_trans_perm = (fun s1 s2 s3 i j -> ())

let snoc = (fun s x -> (FStar_Seq.append s (FStar_Seq.create 1 x)))

let rec seq_find_aux = (fun f l ctr -> (match (ctr) with
| 0 -> begin
None
end
| _7_609 -> begin
(let i = (ctr - 1)
in if (f (FStar_Seq.index l i)) then begin
(let _7_611 = ()
in Some ((FStar_Seq.index l i)))
end else begin
(seq_find_aux f l i)
end)
end))

let seq_find = (fun f l -> (let _7_623 = ()
in (seq_find_aux f l (FStar_Seq.length l))))




