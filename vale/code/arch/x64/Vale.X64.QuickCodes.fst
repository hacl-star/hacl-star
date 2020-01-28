module Vale.X64.QuickCodes
open FStar.Mul
open Vale.Arch.HeapImpl
module Map16 = Vale.Lib.Map16

#reset-options "--initial_ifuel 1 --z3rlimit 30"

let lemma_label_Type0 (r:range) (msg:string) (p:Type0) : Lemma
  (requires True) (ensures label r msg p ==> p)
  = ()

let lemma_label_bool r msg b = lemma_label_Type0 r msg b

let rec empty_list_is_small #a x =
  match x with
  | [] -> ()
  | h::t -> empty_list_is_small t

let state_mod_eq (m:mod_t) (s1 s2:vale_state) =
  match m with
  | Mod_None -> True
  | Mod_ok -> s1.vs_ok == s2.vs_ok
  | Mod_reg r -> eval_reg r s1 == eval_reg r s2
  | Mod_flags -> s1.vs_flags == s2.vs_flags
  | Mod_mem -> s1.vs_heap.vf_heap == s2.vs_heap.vf_heap
  | Mod_mem_layout -> s1.vs_heap.vf_layout == s2.vs_heap.vf_layout
  | Mod_mem_heaplet n -> Map16.sel s1.vs_heap.vf_heaplets n == Map16.sel s2.vs_heap.vf_heaplets n
  | Mod_stack -> s1.vs_stack == s2.vs_stack
  | Mod_stackTaint -> s1.vs_stackTaint == s2.vs_stackTaint

let rec update_state_mods_refl (mods:mods_t) (s:vale_state) : Lemma
  (ensures state_eq (update_state_mods mods s s) s)
  =
  match mods with
  | [] -> ()
  | _::mods -> update_state_mods_refl mods s

let rec update_state_mods_not1 (mods:mods_t) (s' s:vale_state) (m0:mod_t) : Lemma
  (requires not (mods_contains1 mods m0))
  (ensures state_mod_eq m0 s (update_state_mods mods s' s))
  =
  match mods with
  | [] -> ()
  | _::mods -> update_state_mods_not1 mods s' s m0

let update_state_mods_from1 (mods:mods_t) (s' s:vale_state) (m0:mod_t) : Lemma
  (requires state_mod_eq m0 s' (update_state_mods mods s' s))
  (ensures mods_contains1 mods m0 \/ state_mod_eq m0 s s')
  =
  if not (mods_contains1 mods m0) then update_state_mods_not1 mods s' s m0

let rec update_state_mods_to1 (mods:mods_t) (s' s:vale_state) (m0:mod_t) : Lemma
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

let update_state_mods_from (mods:mods_t) (s' s:vale_state) : Lemma
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

let update_state_mods_to (mods:mods_t) (s' s:vale_state) : Lemma
  (requires (
    forall (m0:mod_t).{:pattern mods_contains1 mods m0 \/ state_mod_eq m0 s s'}
      mods_contains1 mods m0 \/ state_mod_eq m0 s s'
  ))
  (ensures state_eq s' (update_state_mods mods s' s))
  =
  let s'' = update_state_mods mods s' s in
  let f1 (m0:mod_t) : Lemma (state_mod_eq m0 s' s'') =
    update_state_mods_to1 mods s' s m0
    in
  f1 Mod_ok;
  f1 Mod_flags;
  f1 Mod_mem;
  f1 Mod_mem_layout;
  f1 Mod_stack;
  f1 Mod_stackTaint;
  let f1_reg (r:reg) : Lemma
    (ensures Regs.sel r s'.vs_regs == Regs.sel r s''.vs_regs)
    [SMTPat (Regs.sel r s'.vs_regs)]
    =
    f1 (Mod_reg r)
    in
  let f1_heaplet (n:heaplet_id) : Lemma
    (ensures Map16.sel s'.vs_heap.vf_heaplets n == Map16.sel s''.vs_heap.vf_heaplets n)
    [SMTPat (Map16.sel s'.vs_heap.vf_heaplets n)]
    =
    f1 (Mod_mem_heaplet n)
    in
  ()

let update_state_mods_trans (mods:mods_t) (s0 s1 s2:vale_state) : Lemma
  (requires update_state_mods mods s1 s0 == s1 /\ update_state_mods mods s2 s1 == s2)
  (ensures update_state_mods mods s2 s0 == s2)
  =
  update_state_mods_from mods s1 s0;
  update_state_mods_from mods s2 s1;
  update_state_mods_to mods s2 s0

let rec update_state_mods_weaken1 (mods mods':mods_t) (s' s:vale_state) (m0:mod_t) : Lemma
  (requires (mods_contains1 mods m0 \/ state_mod_eq m0 s s') /\ mods_contains mods' mods)
  (ensures (mods_contains1 mods' m0 \/ state_mod_eq m0 s s'))
  =
  match mods with
  | [] -> ()
  | _::mods ->
      if mods_contains mods' mods && mods_contains1 mods m0 then
        update_state_mods_weaken1 mods mods' s' s m0

let update_state_mods_weaken (mods mods':mods_t) (s' s:vale_state) : Lemma
  (requires update_state_mods mods s' s == s' /\ mods_contains mods' mods)
  (ensures update_state_mods mods' s' s == s')
  =
  update_state_mods_from mods s' s;
  let f1 (m0:mod_t) : Lemma (mods_contains1 mods' m0 \/ state_mod_eq m0 s s') =
    update_state_mods_weaken1 mods mods' s' s m0
    in
  FStar.Classical.forall_intro f1;
  update_state_mods_to mods' s' s

let call_QPURE
    (#a:Type0) (#cs:codes) (r:range) (msg:string) (pre:((unit -> GTot Type0) -> GTot Type0))
    (l:unit -> PURE unit pre) (qcs:quickCodes a cs) (mods:mods_t) (k:vale_state -> a -> Type0) (s0:vale_state)
  : Lemma
  (requires
    (forall (p:unit -> GTot Type0).{:pattern pre p}
      (wp cs qcs mods k s0 ==> p ()) ==> label r msg (pre p)))
  (ensures wp cs qcs mods k s0)
  =
  l ()

(*
let call_QBindPURE
    (#a #b:Type0) (#cs:codes) (r:range) (msg:string) (pre:((b -> GTot Type0) -> GTot Type0))
    (l:unit -> PURE b pre) (qcs:vale_state -> b -> GTot (quickCodes a cs)) (mods:mods_t)
    (k:vale_state -> a -> Type0) (s0:vale_state)
  : Ghost b
  (requires
    (forall (p:b -> GTot Type0).{:pattern pre p}
      (forall (g:b).{:pattern guard_free (p g)}
        wp cs (qcs s0 g) mods k s0 ==> p g) ==> label r msg (pre p)))
  (ensures fun g -> (wp cs (qcs s0 g) mods k s0))
  =
  l ()
*)

let rec wp_sound #a cs qcs mods k s0 =
  let qcs0 = qcs in
  match qcs with
  | QEmpty g ->
      update_state_mods_refl mods s0;
      let (sN, fN) = va_lemma_empty_total s0 [] in (sN, fN, g)
  | QSeq _ _ qc qcs ->
      let QProc _ _ wp1' proof = qc in
      let c::cs = cs in
      let k' = wp_Seq cs qcs mods k in
      let (sM, fM, gM) = proof s0 k' in
      let (sN, fN, gN) = wp_sound cs qcs mods k sM in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      update_state_mods_weaken qc.mods mods sM s0;
      update_state_mods_trans mods s0 sM sN;
      (sN, fN', gN)
  | QBind _ _ qc qcs ->
      let QProc c' _ wp1' proof = qc in
      let c::cs = cs in
      let k' = wp_Bind cs qcs mods k in
      let (sM, fM, gM) = proof s0 k' in
      let (sN, fN, gN) = wp_sound cs (qcs sM gM) mods k sM in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      update_state_mods_weaken qc.mods mods sM s0;
      update_state_mods_trans mods s0 sM sN;
      (sN, fN', gN)
  | QGetState f ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      let (sN, fN, gN) = wp_sound cs (f sM) mods k sM in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      (sN, fN', gN)
  | QPURE r msg pre l qcs' ->
      call_QPURE r msg pre l qcs' mods k s0;
      wp_sound cs qcs' mods k s0
(*
  | QBindPURE b r msg pre l qcs' ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      let g = call_QBindPURE r msg pre l qcs' mods k s0 in
      let (sN, fN, gN) = wp_sound cs (qcs' s0 g) mods k s0 in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      (sN, fN', gN)
*)
  | QLemma _ _ pre post l qcs' ->
      l ();
      wp_sound cs qcs' mods k s0
  | QGhost b _ _ pre post l qcs' ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      let g = l () in
      let (sN, fN, gN) = wp_sound cs (qcs' g) mods k s0 in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      (sN, fN', gN)
  | QAssertBy r msg p qcsBy qcs ->
      empty_list_is_small cs;
      let _ = wp_sound [] qcsBy mods (k_AssertBy p) s0 in
      wp_sound cs qcs mods k s0

let qblock_proof #a #cs qcs mods s0 k =
  wp_sound cs (qcs s0) mods k s0

let qInlineIf_proof #a #c1 #c2 b qc1 qc2 mods s0 k =
  if b then
  (
    let (sM, f0, g) = QProc?.proof qc1 s0 k in
    update_state_mods_weaken qc1.mods mods sM s0;
    (sM, f0, g)
  )
  else
  (
    let (sM, f0, g) = QProc?.proof qc2 s0 k in
    update_state_mods_weaken qc2.mods mods sM s0;
    (sM, f0, g)
  )

let qIf_proof #a #c1 #c2 b qc1 qc2 mods s0 k =
  ( match b with
    | Cmp_eq o1 o2 -> lemma_valid_cmp_eq s0 o1 o2; lemma_cmp_eq s0 o1 o2
    | Cmp_ne o1 o2 -> lemma_valid_cmp_ne s0 o1 o2; lemma_cmp_ne s0 o1 o2
    | Cmp_le o1 o2 -> lemma_valid_cmp_le s0 o1 o2; lemma_cmp_le s0 o1 o2
    | Cmp_ge o1 o2 -> lemma_valid_cmp_ge s0 o1 o2; lemma_cmp_ge s0 o1 o2
    | Cmp_lt o1 o2 -> lemma_valid_cmp_lt s0 o1 o2; lemma_cmp_lt s0 o1 o2
    | Cmp_gt o1 o2 -> lemma_valid_cmp_gt s0 o1 o2; lemma_cmp_gt s0 o1 o2
  );
  if eval_cmp s0 b then
  (
    let (sM, f0, g) = QProc?.proof qc1 s0 k in
    va_lemma_ifElseTrue_total (cmp_to_ocmp b) c1 c2 s0 f0 sM;
    update_state_mods_weaken qc1.mods mods sM s0;
    (sM, f0, g)
  )
  else
  (
    let (sM, f0, g) = QProc?.proof qc2 s0 k in
    va_lemma_ifElseFalse_total (cmp_to_ocmp b) c1 c2 s0 f0 sM;
    update_state_mods_weaken qc2.mods mods sM s0;
    (sM, f0, g)
  )

let rec qWhile_proof_rec
    (#a #d:Type) (#c:code) (b:cmp) (qc:a -> quickCode a c) (mods:mods_t) (inv:vale_state -> a -> Type0)
    (dec:vale_state -> a -> d) (s0 s1:vale_state) (g1:a) (f1:fuel) (k:vale_state -> a -> Type0)
  : Ghost (vale_state & va_fuel & a)
  (requires
    state_inv s1 /\
    wp_While b qc mods inv dec g1 s1 k /\
    eval_while_inv (While (cmp_to_ocmp b) c) s0 f1 s1 /\
    update_state_mods mods s1 s0 == s1)
  (ensures fun (s2, f2, g2) ->
    eval_code (While (cmp_to_ocmp b) c) s0 f2 s2 /\
    update_state_mods mods s2 s0 == s2 /\ state_inv s2 /\ k s2 g2
  )
  (decreases (dec s1 g1))
  =
  let ob = cmp_to_ocmp b in
  if eval_cmp s1 b then
  (
    let inv2 = wp_While_inv qc mods inv dec s1 g1 in
    let wp = QProc?.wp (qc g1) in
    let (s2, f2) = va_lemma_whileTrue_total ob c s0 s1 f1 in
    let (sc, fc, gc) = QProc?.proof (qc g1) s2 inv2 in
    let fN = va_lemma_whileMerge_total (While ob c) s0 f2 s2 fc sc in
    update_state_mods_weaken (qc g1).mods mods sc s2;
    update_state_mods_trans mods s0 s2 sc;
    qWhile_proof_rec b qc mods inv dec s0 sc gc fN k
  )
  else
  (
    let (s2, f2) = va_lemma_whileFalse_total ob c s0 s1 f1 in
    (s2, f2, g1)
  )

let qWhile_proof #a #d #c b qc mods inv dec g0 s0 k =
  let ob = cmp_to_ocmp b in
  let (s1, f1) = va_lemma_while_total ob c s0 in
  update_state_mods_refl mods s0;
  qWhile_proof_rec b qc mods inv dec s0 s1 g0 f1 k

let qAssertLemma p = fun () -> ()
let qAssumeLemma p = fun () -> assume p
let qAssertSquashLemma p = fun () -> ()

//let qAssertByLemma #a p qcs mods s0 =
//  fun () -> let _ = wp_sound [] qcs mods (fun _ _ -> p) s0 in ()

let wp_sound_code #a c qc k s0 =
  let QProc c _ wp proof = qc in
  proof s0 k

let rec lemma_regs_match_file (r0:Regs.t) (r1:Regs.t) (rf:reg_file_id) (k:nat{k <= n_regs rf}) : Lemma
  (requires regs_match_file r0 r1 rf k)
  (ensures (forall (i:nat).{:pattern (Reg rf i)} i < k ==>
    (let r = Reg rf i in Regs.sel r r0 == Regs.sel r r1)))
  =
  if k > 0 then lemma_regs_match_file r0 r1 rf (k - 1)

let rec lemma_regs_match (r0:Regs.t) (r1:Regs.t) (k:nat{k <= n_reg_files}) : Lemma
  (requires regs_match r0 r1 k)
  (ensures (forall (i j:nat).{:pattern (Reg i j)} i < k /\ j < n_regs i ==>
    (let r = Reg i j in Regs.sel r r0 == Regs.sel r r1)))
  =
  if k > 0 then (lemma_regs_match_file r0 r1 (k - 1) (n_regs (k - 1)); lemma_regs_match r0 r1 (k - 1))

let lemma_state_match s0 s1 =
  lemma_regs_match s0.vs_regs s1.vs_regs n_reg_files;
  assert (Regs.equal s0.vs_regs s1.vs_regs)

let wp_sound_code_wrap (#a:Type0) (c:code) (qc:quickCode a c) (s0:vale_state) (k:(s0':vale_state{s0 == s0'}) -> vale_state -> a -> Type0) :
  Ghost (vale_state & fuel & a)
    (t_require s0 /\ wp_sound_code_pre qc s0 k)
    (wp_sound_code_post qc s0 k)
  =
  wp_sound_code c qc (k s0) s0

let assert_normal (p:Type) : Lemma
  (requires normal p)
  (ensures p)
  =
  ()

let va_wp_sound_code_norm #a c qc s0 k =
  assert_normal (wp_sound_code_pre qc s0 k);
  wp_sound_code_wrap c qc s0 k
