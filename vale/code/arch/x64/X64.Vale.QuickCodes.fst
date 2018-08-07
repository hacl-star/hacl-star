module X64.Vale.QuickCodes

#reset-options "--initial_ifuel 1 --z3rlimit 30"

let lemma_label_Type0 (r:range) (msg:string) (p:Type0) : Lemma
  (requires True) (ensures label r msg p ==> p)
  = ()

let lemma_label_bool r msg b = lemma_label_Type0 r msg b

let rec wp_monotone #a cs qcs k1 k2 s0 =
  match qcs with
  | QEmpty g -> ()
  | QSeq _ _ qc qcs ->
      let QProc _ wp1' monotone _ _ = qc in
      let c::cs = cs in
      let k1' = wp_Seq cs qcs k1 in
      let k2' = wp_Seq cs qcs k2 in
      let f s g : Lemma (k1' s g ==> k2' s g) =
        wp_monotone cs qcs k1 k2 s
        in
      FStar.Classical.forall_intro_2 f;
      assert (forall s g. k1' s g ==> k2' s g);
      monotone s0 k1' k2'
  | QBind _ _ qc qcs ->
      let QProc c' wp1' monotone _ _ = qc in
      let c::cs = cs in
      let k1' = wp_Bind cs qcs k1 in
      let k2' = wp_Bind cs qcs k2 in
      let f s g : Lemma (k1' s g ==> k2' s g) =
        wp_monotone cs (qcs s g) k1 k2 s
        in
      FStar.Classical.forall_intro_2 f;
      monotone s0 k1' k2'
  | QGetState f ->
      let c::cs = cs in
      wp_monotone cs (f s0) k1 k2 s0
  | QPURE _ _ pre l qcs' ->
      wp_monotone cs qcs' k1 k2 s0
  | QLemma _ _ pre post l qcs' ->
      wp_monotone cs qcs' k1 k2 s0

let call_QLemma (#a:Type0) (#cs:codes) (r:range) (msg:string) (pre:((unit -> GTot Type0) -> GTot Type0)) (l:unit -> PURE unit pre) (qcs:quickCodes a cs) (k:state -> a -> Type0) (s0:state) :
  Lemma
  (requires (forall (p:unit -> GTot Type0). (wp cs qcs k s0 ==> p ()) ==> label r msg (pre p)))
  (ensures (wp cs qcs k s0))
  =
  l ()

let rec wp_compute #a cs qcs s0 =
  match qcs with
  | QEmpty g ->
      let (sN, fN) = va_lemma_empty_total s0 [] in (sN, fN, g)
  | QSeq _ _ qc qcs ->
      let QProc _ wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Seq cs qcs k_true in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      let (sN, fN, gN) = wp_compute cs qcs sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QBind _ _ qc qcs ->
      let QProc c' wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Bind cs qcs k_true in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      let (sN, fN, gN) = wp_compute cs (qcs sM gM) sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QGetState f ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      let (sN, fN, gN) = wp_compute cs (f sM) sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QPURE r msg pre l qcs' ->
      assert (wp cs qcs k_true s0);
      call_QLemma r msg pre l qcs' k_true s0;
      wp_compute cs qcs' s0
  | QLemma _ _ pre post l qcs' ->
      l ();
      wp_compute cs qcs' s0

let rec wp_sound #a cs qcs k s0 =
  match qcs with
  | QEmpty g ->
      let (sN, fN) = va_lemma_empty_total s0 [] in ()
  | QSeq _ _ qc qcs ->
      let QProc _ wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Seq cs qcs k in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      wp_monotone cs qcs k k_true sM;
      let (sN, fN, gN) = wp_compute cs qcs sM in
      wp_sound cs qcs k sM;
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      ()
  | QBind _ _ qc qcs ->
      let QProc c' wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Bind cs qcs k in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      wp_monotone cs (qcs sM gM) k k_true sM;
      let (sN, fN, gN) = wp_compute cs (qcs sM gM) sM in
      wp_sound cs (qcs sM gM) k sM;
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      ()
  | QGetState f ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      wp_sound cs (f sM) k sM;
      wp_monotone cs (f sM) k k_true sM;
      let (sN, fN, gN) = wp_compute cs (f sM) sM in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      ()
  | QPURE r msg pre l qcs' ->
      wp_monotone cs qcs k k_true s0;
      call_QLemma r msg pre l qcs' k_true s0;
      call_QLemma r msg pre l qcs' k s0;
      wp_sound cs qcs' k s0;
      ()
  | QLemma _ _ pre post l qcs' ->
      wp_monotone cs qcs k k_true s0;
      l ();
      wp_sound cs qcs' k s0;
      ()

let qblock_monotone #a #cs qcs s0 k1 k2 =
  wp_monotone cs (qcs s0) k1 k2 s0

let qblock_compute #a #cs qcs s0 =
  wp_compute cs (qcs s0) s0

let qblock_proof #a #cs qcs s0 k =
  wp_monotone cs (qcs s0) k k_true s0;
  let (sM, f0, g) = wp_compute cs (qcs s0) s0 in
  wp_sound cs (qcs s0) k s0

let qInlineIf_monotone #a #c1 #c2 b qc1 qc2 s0 k1 k2 =
  if b then
    QProc?.monotone qc1 s0 k1 k2
  else
    QProc?.monotone qc2 s0 k1 k2

let qInlineIf_compute #a #c1 #c2 b qc1 qc2 s0 =
  if b then
    QProc?.compute qc1 s0
  else
    QProc?.compute qc2 s0

let qInlineIf_proof #a #c1 #c2 b qc1 qc2 s0 k =
  if b then
    QProc?.proof qc1 s0 k
  else
    QProc?.proof qc2 s0 k

let qIf_monotone #a #c1 #c2 b qc1 qc2 s0 k1 k2 =
  if eval_cmp s0 b then
    QProc?.monotone qc1 s0 k1 k2
  else
    QProc?.monotone qc2 s0 k1 k2

let qIf_compute #a #c1 #c2 b qc1 qc2 s0 =
  if eval_cmp s0 b then
    QProc?.compute qc1 s0
  else
    QProc?.compute qc2 s0

let qIf_proof #a #c1 #c2 b qc1 qc2 s0 k =
  ( match b with
    | Cmp_eq o1 o2 -> lemma_valid_cmp_eq s0 o1 o2; lemma_cmp_eq s0 o1 o2
    | Cmp_ne o1 o2 -> lemma_valid_cmp_ne s0 o1 o2; lemma_cmp_ne s0 o1 o2
    | Cmp_le o1 o2 -> lemma_valid_cmp_le s0 o1 o2; lemma_cmp_le s0 o1 o2
    | Cmp_ge o1 o2 -> lemma_valid_cmp_ge s0 o1 o2; lemma_cmp_ge s0 o1 o2
    | Cmp_lt o1 o2 -> lemma_valid_cmp_lt s0 o1 o2; lemma_cmp_lt s0 o1 o2
    | Cmp_gt o1 o2 -> lemma_valid_cmp_gt s0 o1 o2; lemma_cmp_gt s0 o1 o2
  );
  qIf_monotone b qc1 qc2 s0 k k_true;
  let (sM, f0, g) = qIf_compute b qc1 qc2 s0 in
  if eval_cmp s0 b then
  (
    QProc?.proof qc1 s0 k;
    va_lemma_ifElseTrue_total (cmp_to_ocmp b) c1 c2 s0 f0 sM
  )
  else
  (
    QProc?.proof qc2 s0 k;
    va_lemma_ifElseFalse_total (cmp_to_ocmp b) c1 c2 s0 f0 sM
  )

let qAssertLemma p = fun () -> ()
let qAssumeLemma p = fun () -> assume p

let qAssertByLemma #a p qcs s0 =
  fun () -> wp_sound [] qcs (fun _ _ -> p) s0

let wp_sound_code #a c qc k s0 =
  let QProc c wp monotone compute proof = qc in
  monotone s0 k k_true;
  let (sM, f0, g) = compute s0 in
  proof s0 k;
  (sM, f0, g)

let wp_sound_wrap #a cs qcs s0 k = wp_sound cs qcs (k s0) s0; wp_monotone cs qcs (k s0) k_true s0; wp_compute cs qcs s0
let wp_sound_code_wrap #a c qc s0 k = wp_sound_code c qc (k s0) s0

irreducible
val wp_wrap_monotone (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (update:state -> state -> state) (post:state -> state -> Type0) (k1:state -> a -> Type0) (k2:state -> a -> Type0) (s0:state) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp_wrap cs qcs update post k1 s0 ==> wp_wrap cs qcs update post k2 s0)
let wp_wrap_monotone #a cs qcs update post k1 k2 s0 =
  wp_monotone cs qcs (wp_final_k (update s0) post k1) (wp_final_k (update s0) post k2) s0

let wp_wrap_compute (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (update:state -> state -> state) (post:state -> state -> Type0) (s0:state) :
  Ghost ((sN:state) * (fN:fuel) * (g:a))
  (requires wp_wrap cs qcs update post k_true s0)
  (ensures fun _ -> True) =
  wp_monotone cs qcs (wp_final_k (update s0) post k_true) k_true s0;
  wp_compute cs qcs s0

irreducible
val wp_wrap_sound (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (update:state -> state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (s0:state) : Lemma
  (requires wp_wrap cs qcs update post k s0)
  (ensures (
    wp_wrap_monotone cs qcs update post k k_true s0;
    let (sN, fN, gN) = wp_wrap_compute cs qcs update post s0 in
    eval (Block cs) s0 fN sN /\ sN == update s0 sN /\ k sN gN
  ))
let wp_wrap_sound #a cs qcs update post k s0 =
  wp_monotone cs qcs (wp_final_k (update s0) post k) k s0;
  wp_wrap_monotone cs qcs update post k k_true s0;
  wp_sound cs qcs k s0;
  wp_sound cs qcs (wp_final_k (update s0) post k_true) s0;
  ()

let wp_run #a cs qcs s0 update post =
  assert (wp_wrap cs qcs update post k_true s0);
  let f (k:state -> a -> Type0) : Lemma (wp_wrap cs qcs update post k s0 ==> wp_wrap cs qcs update post k_true s0) =
    wp_wrap_monotone cs qcs update post k k_true s0
    in
  FStar.Classical.forall_intro f;
  let (sN, fN, gN) = wp_wrap_compute cs qcs update post s0 in
  let f (p:state * fuel * a -> Type) (_:squash (wp_GHOST (Block cs) s0 update (fun k -> wp_wrap cs qcs update post k s0) p)) :
    Lemma (p (sN, fN, gN)) =
    let k sN gN = (forall (fN:fuel). eval (Block cs) s0 fN sN /\ sN == update s0 sN ==> p (sN, fN, gN)) in
    wp_wrap_sound cs qcs update post k s0
    in
  FStar.Classical.forall_impl_intro f;
  (sN, fN, gN)

irreducible
val wp_wrap_monotone_code (#a:Type0) (c:code) (qc:quickCode a c) (update:state -> state -> state) (post:state -> state -> Type0) (k1:state -> a -> Type0) (k2:state -> a -> Type0) (s0:state) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp_wrap_code c qc update post k1 s0 ==> wp_wrap_code c qc update post k2 s0)
let wp_wrap_monotone_code #a c qc update post k1 k2 s0 =
  let QProc _ wp monotone compute proof = qc in
  monotone s0 (wp_final_k (update s0) post k1) (wp_final_k (update s0) post k2)

let wp_wrap_compute_code (#a:Type0) (c:code) (qc:quickCode a c) (update:state -> state -> state) (post:state -> state -> Type0) (s0:state) :
  Ghost ((sN:state) * (fN:fuel) * (g:a))
  (requires wp_wrap_code c qc update post k_true s0)
  (ensures fun _ -> True) =
  let QProc _ wp monotone compute proof = qc in
  monotone s0 (wp_final_k (update s0) post k_true) k_true;
  compute s0

irreducible
val wp_wrap_sound_code (#a:Type0) (c:code) (qc:quickCode a c) (update:state -> state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (s0:state) : Lemma
  (requires wp_wrap_code c qc update post k s0)
  (ensures (
    wp_wrap_monotone_code c qc update post k k_true s0;
    let (sN, fN, gN) = wp_wrap_compute_code c qc update post s0 in
    eval c s0 fN sN /\ sN == update s0 sN /\ k sN gN
  ))
let wp_wrap_sound_code #a c qc update post k s0 =
  let QProc _ wp monotone compute proof = qc in
  monotone s0 (wp_final_k (update s0) post k) k;
  wp_wrap_monotone_code c qc update post k k_true s0;
  proof s0 k;
  proof s0 (wp_final_k (update s0) post k_true);
  ()

let wp_run_code #a c qc s0 update post =
  let QProc _ wp monotone compute proof = qc in
  assert (wp_wrap_code c qc update post k_true s0);
  let f (k:state -> a -> Type0) : Lemma (wp_wrap_code c qc update post k s0 ==> wp_wrap_code c qc update post k_true s0) =
    wp_wrap_monotone_code c qc update post k k_true s0
    in
  FStar.Classical.forall_intro f;
  let (sN, fN, gN) = wp_wrap_compute_code c qc update post s0 in
  let f (p:state * fuel * a -> Type) (_:squash (wp_GHOST c s0 update (fun k -> wp_wrap_code c qc update post k s0) p)) :
    Lemma (p (sN, fN, gN)) =
    let k sN gN = (forall (fN:fuel). eval c s0 fN sN /\ sN == update s0 sN ==> p (sN, fN, gN)) in
    wp_wrap_sound_code c qc update post k s0
    in
  FStar.Classical.forall_impl_intro f;
  (sN, fN, gN)

let wp_sound_norm = wp_sound_wrap
let wp_sound_code_norm = wp_sound_code_wrap
let wp_run_norm = wp_run
