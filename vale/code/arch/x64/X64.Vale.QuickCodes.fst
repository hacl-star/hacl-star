module X64.Vale.QuickCodes

#reset-options "--initial_ifuel 1 --z3rlimit 30"

let lemma_label_Type0 (r:range) (msg:string) (p:Type0) : Lemma
  (requires True) (ensures label r msg p ==> p)
  = ()

let lemma_label_bool r msg b = lemma_label_Type0 r msg b

let state_mod_eq (m:mod_t) (s1 s2:state) =
  match m with
  | Mod_None -> True
  | Mod_ok -> s1.ok == s2.ok
  | Mod_reg r -> eval_reg r s1 == eval_reg r s2
  | Mod_xmm x -> eval_xmm x s1 == eval_xmm x s2
  | Mod_flags -> s1.flags == s2.flags
  | Mod_mem -> s1.mem == s2.mem
  | Mod_stack -> s1.stack == s2.stack
  | Mod_memTaint -> s1.memTaint == s2.memTaint

let rec update_state_mods_refl (mods:mods_t) (s:state) : Lemma
  (ensures state_eq (update_state_mods mods s s) s)
  =
  match mods with
  | [] -> ()
  | _::mods -> update_state_mods_refl mods s

let rec update_state_mods_not1 (mods:mods_t) (s' s:state) (m0:mod_t) : Lemma
  (requires not (mods_contains1 mods m0))
  (ensures state_mod_eq m0 s (update_state_mods mods s' s))
  =
  match mods with
  | [] -> ()
  | _::mods -> update_state_mods_not1 mods s' s m0

let update_state_mods_from1 (mods:mods_t) (s' s:state) (m0:mod_t) : Lemma
  (requires state_mod_eq m0 s' (update_state_mods mods s' s))
  (ensures mods_contains1 mods m0 \/ state_mod_eq m0 s s')
  =
  if not (mods_contains1 mods m0) then update_state_mods_not1 mods s' s m0

let rec update_state_mods_to1 (mods:mods_t) (s' s:state) (m0:mod_t) : Lemma
  (requires mods_contains1 mods m0 \/ state_mod_eq m0 s s')
  (ensures state_mod_eq m0 s' (update_state_mods mods s' s))
  =
  match mods with
  | [] -> ()
  | r::mods' ->
      let b = r =!= m0 \/ state_mod_eq m0 s s' in
      let goal (_:squash (b \/ ~b)) : Type0 = state_mod_eq m0 s' (update_state_mods mods s' s) in
      let l1 (_:squash b) : Lemma (goal ()) = update_state_mods_to1 mods' s' s m0 in
      let l2 (_:squash (~b)) : Lemma (goal ()) = () in
      FStar.Classical.or_elim #b #(~b) #goal l1 l2

let update_state_mods_from (mods:mods_t) (s' s:state) : Lemma
  (requires update_state_mods mods s' s == s')
  (ensures (
    forall (m0:mod_t).{:pattern mods_contains1 mods m0 \/ state_mod_eq m0 s s'}
      mods_contains1 mods m0 \/ state_mod_eq m0 s s'
  ))
  =
  let f1 (m0:mod_t) : Lemma (mods_contains1 mods m0 \/ state_mod_eq m0 s s') =
    update_state_mods_from1 mods s' s m0
    in
  FStar.Classical.forall_intro f1

let update_state_mods_to (mods:mods_t) (s' s:state) : Lemma
  (requires (
    forall (m0:mod_t).{:pattern mods_contains1 mods m0 \/ state_mod_eq m0 s s'}
      mods_contains1 mods m0 \/ state_mod_eq m0 s s'
  ))
  (ensures state_eq s' (update_state_mods mods s' s))
  =
  let f1 (m0:mod_t) : Lemma (state_mod_eq m0 s' (update_state_mods mods s' s)) =
    update_state_mods_to1 mods s' s m0
    in
  let f1_reg (r:reg) : Lemma (state_mod_eq (Mod_reg r) s' (update_state_mods mods s' s)) = f1 (Mod_reg r) in
  let f1_xmm (x:xmm) : Lemma (state_mod_eq (Mod_xmm x) s' (update_state_mods mods s' s)) = f1 (Mod_xmm x) in
  f1 (Mod_ok);
  FStar.Classical.forall_intro f1_reg;
  FStar.Classical.forall_intro f1_xmm;
  f1 (Mod_flags);
  f1 (Mod_mem);
  f1 (Mod_stack);
  f1 (Mod_memTaint);
  ()

let update_state_mods_trans (mods:mods_t) (s0 s1 s2:state) : Lemma
  (requires update_state_mods mods s1 s0 == s1 /\ update_state_mods mods s2 s1 == s2)
  (ensures update_state_mods mods s2 s0 == s2)
  =
  update_state_mods_from mods s1 s0;
  update_state_mods_from mods s2 s1;
  update_state_mods_to mods s2 s0

let rec update_state_mods_weaken1 (mods mods':mods_t) (s' s:state) (m0:mod_t) : Lemma
  (requires (mods_contains1 mods m0 \/ state_mod_eq m0 s s') /\ mods_contains mods' mods)
  (ensures (mods_contains1 mods' m0 \/ state_mod_eq m0 s s'))
  =
  match mods with
  | [] -> ()
  | _::mods ->
      if mods_contains mods' mods && mods_contains1 mods m0 then
        update_state_mods_weaken1 mods mods' s' s m0

let update_state_mods_weaken (mods mods':mods_t) (s' s:state) : Lemma
  (requires update_state_mods mods s' s == s' /\ mods_contains mods' mods)
  (ensures update_state_mods mods' s' s == s')
  =
  update_state_mods_from mods s' s;
  let f1 (m0:mod_t) : Lemma (mods_contains1 mods' m0 \/ state_mod_eq m0 s s') =
    update_state_mods_weaken1 mods mods' s' s m0
    in
  FStar.Classical.forall_intro f1;
  update_state_mods_to mods' s' s

let rec wp_monotone #a cs qcs mods k1 k2 s0 =
  match qcs with
  | QEmpty g -> ()
  | QSeq _ _ qc qcs ->
      let QProc _ _ wp1' monotone _ _ = qc in
      let c::cs = cs in
      let k1' = wp_Seq cs qcs mods k1 in
      let k2' = wp_Seq cs qcs mods k2 in
      let f s g : Lemma (k1' s g ==> k2' s g) =
        wp_monotone cs qcs mods k1 k2 s
        in
      FStar.Classical.forall_intro_2 f;
      assert (forall s g. k1' s g ==> k2' s g);
      monotone s0 k1' k2'
  | QBind _ _ qc qcs ->
      let QProc c' _ wp1' monotone _ _ = qc in
      let c::cs = cs in
      let k1' = wp_Bind cs qcs mods k1 in
      let k2' = wp_Bind cs qcs mods k2 in
      let f s g : Lemma (k1' s g ==> k2' s g) =
        wp_monotone cs (qcs s g) mods k1 k2 s
        in
      FStar.Classical.forall_intro_2 f;
      monotone s0 k1' k2'
  | QGetState f ->
      let c::cs = cs in
      wp_monotone cs (f s0) mods k1 k2 s0
  | QPURE _ _ pre l qcs' ->
      wp_monotone cs qcs' mods k1 k2 s0
  | QLemma _ _ pre post l qcs' ->
      wp_monotone cs qcs' mods k1 k2 s0

let call_QLemma (#a:Type0) (#cs:codes) (r:range) (msg:string) (pre:((unit -> GTot Type0) -> GTot Type0)) (l:unit -> PURE unit pre) (qcs:quickCodes a cs) (mods:mods_t) (k:state -> a -> Type0) (s0:state) :
  Lemma
  (requires (forall (p:unit -> GTot Type0). (wp cs qcs mods k s0 ==> p ()) ==> label r msg (pre p)))
  (ensures (wp cs qcs mods k s0))
  =
  l ()

let rec wp_compute #a cs qcs mods s0 =
  match qcs with
  | QEmpty g ->
      let (sN, fN) = va_lemma_empty_total s0 [] in (sN, fN, g)
  | QSeq _ _ qc qcs ->
      let QProc _ _ wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Seq cs qcs mods k_true in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      let (sN, fN, gN) = wp_compute cs qcs mods sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QBind _ _ qc qcs ->
      let QProc c' _ wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Bind cs qcs mods k_true in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      let (sN, fN, gN) = wp_compute cs (qcs sM gM) mods sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QGetState f ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      let (sN, fN, gN) = wp_compute cs (f sM) mods sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QPURE r msg pre l qcs' ->
      assert (wp cs qcs mods k_true s0);
      call_QLemma r msg pre l qcs' mods k_true s0;
      wp_compute cs qcs' mods s0
  | QLemma _ _ pre post l qcs' ->
      l ();
      wp_compute cs qcs' mods s0

let rec wp_sound #a cs qcs mods k s0 =
  let qcs0 = qcs in
  match qcs with
  | QEmpty g ->
      update_state_mods_refl mods s0;
      let (sN, fN) = va_lemma_empty_total s0 [] in ()
  | QSeq _ _ qc qcs ->
      let QProc _ _ wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Seq cs qcs mods k in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      wp_monotone cs qcs mods k k_true sM;
      let (sN, fN, gN) = wp_compute cs qcs mods sM in
      wp_sound cs qcs mods k sM;
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      update_state_mods_weaken qc.mods mods sM s0;
      update_state_mods_trans mods s0 sM sN;
      wp_monotone (c::cs) qcs0 mods k k_true s0;
      ()
  | QBind _ _ qc qcs ->
      let QProc c' _ wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Bind cs qcs mods k in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      wp_monotone cs (qcs sM gM) mods k k_true sM;
      let (sN, fN, gN) = wp_compute cs (qcs sM gM) mods sM in
      wp_sound cs (qcs sM gM) mods k sM;
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      update_state_mods_weaken qc.mods mods sM s0;
      update_state_mods_trans mods s0 sM sN;
      wp_monotone (c::cs) qcs0 mods k k_true s0;
      ()
  | QGetState f ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      wp_sound cs (f sM) mods k sM;
      wp_monotone cs (f sM) mods k k_true sM;
      let (sN, fN, gN) = wp_compute cs (f sM) mods sM in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      ()
  | QPURE r msg pre l qcs' ->
      wp_monotone cs qcs mods k k_true s0;
      call_QLemma r msg pre l qcs' mods k_true s0;
      call_QLemma r msg pre l qcs' mods k s0;
      wp_sound cs qcs' mods k s0;
      ()
  | QLemma _ _ pre post l qcs' ->
      wp_monotone cs qcs mods k k_true s0;
      l ();
      wp_sound cs qcs' mods k s0;
      ()

let qblock_monotone #a #cs qcs mods s0 k1 k2 =
  wp_monotone cs (qcs s0) mods k1 k2 s0

let qblock_compute #a #cs qcs mods s0 =
  wp_compute cs (qcs s0) mods s0

let qblock_proof #a #cs qcs mods s0 k =
  wp_monotone cs (qcs s0) mods k k_true s0;
  let (sM, f0, g) = wp_compute cs (qcs s0) mods s0 in
  wp_sound cs (qcs s0) mods k s0;
  ()

let qInlineIf_monotone #a #c1 #c2 b qc1 qc2 mods s0 k1 k2 =
  if b then
    QProc?.monotone qc1 s0 k1 k2
  else
    QProc?.monotone qc2 s0 k1 k2

let qInlineIf_compute #a #c1 #c2 b qc1 qc2 mods s0 =
  if b then
    QProc?.compute qc1 s0
  else
    QProc?.compute qc2 s0

let qInlineIf_proof #a #c1 #c2 b qc1 qc2 mods s0 k =
  qInlineIf_monotone b qc1 qc2 mods s0 k k_true;
  let (sM, f0, g) = qInlineIf_compute b qc1 qc2 mods s0 in
  if b then
  (
    QProc?.proof qc1 s0 k;
    update_state_mods_weaken qc1.mods mods sM s0
  )
  else
  (
    QProc?.proof qc2 s0 k;
    update_state_mods_weaken qc2.mods mods sM s0
  )

let qIf_monotone #a #c1 #c2 b qc1 qc2 mods s0 k1 k2 =
  if eval_cmp s0 b then
    QProc?.monotone qc1 s0 k1 k2
  else
    QProc?.monotone qc2 s0 k1 k2

let qIf_compute #a #c1 #c2 b qc1 qc2 mods s0 =
  if eval_cmp s0 b then
    QProc?.compute qc1 s0
  else
    QProc?.compute qc2 s0

let qIf_proof #a #c1 #c2 b qc1 qc2 mods s0 k =
  ( match b with
    | Cmp_eq o1 o2 -> lemma_valid_cmp_eq s0 o1 o2; lemma_cmp_eq s0 o1 o2
    | Cmp_ne o1 o2 -> lemma_valid_cmp_ne s0 o1 o2; lemma_cmp_ne s0 o1 o2
    | Cmp_le o1 o2 -> lemma_valid_cmp_le s0 o1 o2; lemma_cmp_le s0 o1 o2
    | Cmp_ge o1 o2 -> lemma_valid_cmp_ge s0 o1 o2; lemma_cmp_ge s0 o1 o2
    | Cmp_lt o1 o2 -> lemma_valid_cmp_lt s0 o1 o2; lemma_cmp_lt s0 o1 o2
    | Cmp_gt o1 o2 -> lemma_valid_cmp_gt s0 o1 o2; lemma_cmp_gt s0 o1 o2
  );
  qIf_monotone b qc1 qc2 mods s0 k k_true;
  let (sM, f0, g) = qIf_compute b qc1 qc2 mods s0 in
  if eval_cmp s0 b then
  (
    QProc?.proof qc1 s0 k;
    va_lemma_ifElseTrue_total (cmp_to_ocmp b) c1 c2 s0 f0 sM;
    update_state_mods_weaken qc1.mods mods sM s0
  )
  else
  (
    QProc?.proof qc2 s0 k;
    va_lemma_ifElseFalse_total (cmp_to_ocmp b) c1 c2 s0 f0 sM;
    update_state_mods_weaken qc2.mods mods sM s0
  )

let qWhile_monotone #a #d #c b qc mods inv dec g0 s0 k1 k2 =
  ()

let rec qWhile_compute_rec
    (#a #d:Type) (#c:code) (b:cmp) (qc:a -> quickCode a c) (mods:mods_t) (inv:state -> a -> Type0)
    (dec:state -> a -> d) (s0 s1:state) (g1:a) (f1:fuel)
    : Ghost (state * fuel * a)
      (requires
        wp_While b qc mods inv dec g1 s1 k_true /\
        eval_while_inv (While (cmp_to_ocmp b) c) s0 f1 s1)
      (ensures fun _ -> True)
      (decreases (dec s1 g1))
  =
  let ob = cmp_to_ocmp b in
  if eval_cmp s1 b then
  (
    let inv2 = wp_While_inv qc mods inv dec s1 g1 in
    let wp = QProc?.wp (qc g1) in
    let monotone = QProc?.monotone (qc g1) in
    let proof = QProc?.proof (qc g1) in
    let (s2, f2) = va_lemma_whileTrue_total ob c s0 s1 f1 in
    monotone s2 inv2 k_true;
    proof s2 inv2;
    let (sc, fc, gc) = QProc?.compute (qc g1) s2 in
    let fN = va_lemma_whileMerge_total (While ob c) s0 f2 s2 fc sc in
    qWhile_compute_rec b qc mods inv dec s0 sc gc fN
  )
  else
  (
    let (s2, f2) = va_lemma_whileFalse_total ob c s0 s1 f1 in
    (s2, f2, g1)
  )

let rec qWhile_proof_rec
    (#a #d:Type) (#c:code) (b:cmp) (qc:a -> quickCode a c) (mods:mods_t) (inv:state -> a -> Type0)
    (dec:state -> a -> d) (s0 s1:state) (g1:a) (f1:fuel) (k:state -> a -> Type0)
    : Lemma
      (requires
        wp_While b qc mods inv dec g1 s1 k /\
        eval_while_inv (While (cmp_to_ocmp b) c) s0 f1 s1 /\
        update_state_mods mods s1 s0 == s1)
      (ensures (
        qWhile_monotone b qc mods inv dec g1 s1 k k_true;
        let (s2, f2, g2) = qWhile_compute_rec b qc mods inv dec s0 s1 g1 f1 in
        eval_code (While (cmp_to_ocmp b) c) s0 f2 s2 /\
        update_state_mods mods s2 s0 == s2 /\ k s2 g2
      ))
      (decreases (dec s1 g1))
    =
  let ob = cmp_to_ocmp b in
  if eval_cmp s1 b then
  (
    let inv2 = wp_While_inv qc mods inv dec s1 g1 in
    let wp = QProc?.wp (qc g1) in
    let monotone = QProc?.monotone (qc g1) in
    let compute = QProc?.compute (qc g1) in
    let proof = QProc?.proof (qc g1) in
    let (s2, f2) = va_lemma_whileTrue_total ob c s0 s1 f1 in
    monotone s2 inv2 k_true;
    proof s2 inv2;
    let (sc, fc, gc) = compute s2 in
    let fN = va_lemma_whileMerge_total (While ob c) s0 f2 s2 fc sc in
    update_state_mods_weaken (qc g1).mods mods sc s2;
    update_state_mods_trans mods s0 s2 sc;
    qWhile_proof_rec b qc mods inv dec s0 sc gc fN k
  )
  else
  (
    let _ = va_lemma_whileFalse_total ob c s0 s1 f1 in
    ()
  )

let qWhile_compute #a #d #c b qc mods inv dec g0 s0 =
  let ob = cmp_to_ocmp b in
  let (s1, f1) = va_lemma_while_total ob c s0 in
  qWhile_compute_rec b qc mods inv dec s0 s1 g0 f1

let qWhile_proof #a #d #c b qc mods inv dec g0 s0 k =
  let ob = cmp_to_ocmp b in
  let (s1, f1) = va_lemma_while_total ob c s0 in
  update_state_mods_refl mods s0;
  qWhile_proof_rec b qc mods inv dec s0 s1 g0 f1 k

let qAssertLemma p = fun () -> ()
let qAssumeLemma p = fun () -> assume p

let qAssertByLemma #a p qcs mods s0 =
  fun () -> wp_sound [] qcs mods (fun _ _ -> p) s0

let wp_sound_code #a c qc k s0 =
  let QProc c _ wp monotone compute proof = qc in
  monotone s0 k k_true;
  let (sM, f0, g) = compute s0 in
  proof s0 k;
  (sM, f0, g)

let wp_sound_wrap #a cs qcs mods s0 k =
  wp_sound cs qcs mods (k s0) s0;
  wp_monotone cs qcs mods (k s0) k_true s0;
  wp_compute cs qcs mods s0

let wp_sound_code_wrap #a c qc s0 k = wp_sound_code c qc (k s0) s0

irreducible
val wp_wrap_monotone (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (mods:mods_t) (update:state -> state -> state) (post:state -> state -> Type0) (k1:state -> a -> Type0) (k2:state -> a -> Type0) (s0:state) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp_wrap cs qcs mods update post k1 s0 ==> wp_wrap cs qcs mods update post k2 s0)
let wp_wrap_monotone #a cs qcs mods update post k1 k2 s0 =
  wp_monotone cs qcs mods (wp_final_k (update s0) post k1) (wp_final_k (update s0) post k2) s0

let wp_wrap_compute (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (mods:mods_t) (update:state -> state -> state) (post:state -> state -> Type0) (s0:state) :
  Ghost ((sN:state) * (fN:fuel) * (g:a))
  (requires wp_wrap cs qcs mods update post k_true s0)
  (ensures fun _ -> True) =
  wp_monotone cs qcs mods (wp_final_k (update s0) post k_true) k_true s0;
  wp_compute cs qcs mods s0

irreducible
val wp_wrap_sound (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (mods:mods_t) (update:state -> state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (s0:state) : Lemma
  (requires wp_wrap cs qcs mods update post k s0)
  (ensures (
    wp_wrap_monotone cs qcs mods update post k k_true s0;
    let (sN, fN, gN) = wp_wrap_compute cs qcs mods update post s0 in
    eval (Block cs) s0 fN sN /\ sN == update s0 sN /\ k sN gN
  ))
let wp_wrap_sound #a cs qcs mods update post k s0 =
  wp_monotone cs qcs mods (wp_final_k (update s0) post k) k s0;
  wp_wrap_monotone cs qcs mods update post k k_true s0;
  wp_sound cs qcs mods k s0;
  wp_sound cs qcs mods (wp_final_k (update s0) post k_true) s0;
  ()

let wp_run #a cs qcs mods s0 update post =
  assert (wp_wrap cs qcs mods update post k_true s0);
  let f (k:state -> a -> Type0) : Lemma (wp_wrap cs qcs mods update post k s0 ==> wp_wrap cs qcs mods update post k_true s0) =
    wp_wrap_monotone cs qcs mods update post k k_true s0
    in
  FStar.Classical.forall_intro f;
  let (sN, fN, gN) = wp_wrap_compute cs qcs mods update post s0 in
  let f (p:state * fuel * a -> Type) (_:squash (wp_GHOST (Block cs) s0 update (fun k -> wp_wrap cs qcs mods update post k s0) p)) :
    Lemma (p (sN, fN, gN)) =
    let k sN gN = (forall (fN:fuel). eval (Block cs) s0 fN sN /\ sN == update s0 sN ==> p (sN, fN, gN)) in
    wp_wrap_sound cs qcs mods update post k s0
    in
  FStar.Classical.forall_impl_intro f;
  (sN, fN, gN)

irreducible
val wp_wrap_monotone_code (#a:Type0) (c:code) (qc:quickCode a c) (update:state -> state -> state) (post:state -> state -> Type0) (k1:state -> a -> Type0) (k2:state -> a -> Type0) (s0:state) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp_wrap_code c qc update post k1 s0 ==> wp_wrap_code c qc update post k2 s0)
let wp_wrap_monotone_code #a c qc update post k1 k2 s0 =
  let QProc _ _ wp monotone compute proof = qc in
  monotone s0 (wp_final_k (update s0) post k1) (wp_final_k (update s0) post k2)

let wp_wrap_compute_code (#a:Type0) (c:code) (qc:quickCode a c) (update:state -> state -> state) (post:state -> state -> Type0) (s0:state) :
  Ghost ((sN:state) * (fN:fuel) * (g:a))
  (requires wp_wrap_code c qc update post k_true s0)
  (ensures fun _ -> True) =
  let QProc _ _ wp monotone compute proof = qc in
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
  let QProc _ _ wp monotone compute proof = qc in
  monotone s0 (wp_final_k (update s0) post k) k;
  wp_wrap_monotone_code c qc update post k k_true s0;
  proof s0 k;
  proof s0 (wp_final_k (update s0) post k_true);
  ()

let wp_run_code #a c qc s0 update post =
  let QProc _ _ wp monotone compute proof = qc in
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

let assert_normal (p:Type) : Lemma
  (requires normal p)
  (ensures p)
  =
  ()

let wp_sound_code_norm #a c qc s0 k =
  assert_normal (wp_sound_code_pre qc s0 k);
  wp_sound_code_wrap c qc s0 k

let wp_run_norm = wp_run
