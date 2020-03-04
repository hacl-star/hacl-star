module Vale.X64.QuickCodes
// Optimized weakest precondition generation for 'quick' procedures
open FStar.Mul
open Vale.Def.Prop_s
open Vale.Arch.HeapImpl
open Vale.X64.Machine_s
open Vale.X64.Memory
open Vale.X64.Stack_i
open Vale.X64.State
open Vale.X64.Decls
open Vale.X64.QuickCode

unfold let code = va_code
unfold let codes = va_codes
unfold let fuel = va_fuel
unfold let eval = eval_code

[@va_qattr "opaque_to_smt"]
let labeled_wrap (r:range) (msg:string) (p:Type0) : GTot Type0 = labeled r msg p

// REVIEW: when used inside a function definition, 'labeled' can show up in an SMT query
// as an uninterpreted function.  Make a wrapper around labeled that is interpreted:
[@va_qattr "opaque_to_smt"]
let label (r:range) (msg:string) (p:Type0) : Ghost Type (requires True) (ensures fun q -> q <==> p) =
  assert_norm (labeled_wrap r msg p <==> p);
  labeled_wrap r msg p

val lemma_label_bool (r:range) (msg:string) (b:bool) : Lemma
  (requires label r msg b)
  (ensures b)
  [SMTPat (label r msg b)]

// wrap "precedes" and LexCons to avoid issues with label (precedes ...)
let precedes_wrap (a:lex_t) (b:lex_t) : GTot Type0 = precedes a b
let lexCons (#a:Type) (h:a) (t:lex_t) : lex_t = LexCons h t

[@va_qattr]
let rec mods_contains1 (allowed:mods_t) (found:mod_t) : bool =
  match allowed with
  | [] -> mod_eq Mod_None found
  | h::t -> mod_eq h found || mods_contains1 t found

[@va_qattr]
let rec mods_contains (allowed:mods_t) (found:mods_t) : bool =
  match found with
  | [] -> true
  | h::t -> mods_contains1 allowed h && mods_contains allowed t

[@va_qattr]
let if_code (b:bool) (c1:code) (c2:code) : code = if b then c1 else c2

noeq type quickCodes (a:Type0) : codes -> Type =
| QEmpty: a -> quickCodes a []
| QSeq: #b:Type -> #c:code -> #cs:codes -> r:range -> msg:string ->
    quickCode b c -> quickCodes a cs -> quickCodes a (c::cs)
| QBind: #b:Type -> #c:code -> #cs:codes -> r:range -> msg:string ->
    quickCode b c -> (va_state -> b -> GTot (quickCodes a cs)) -> quickCodes a (c::cs)
| QGetState: #cs:codes -> (va_state -> GTot (quickCodes a cs)) -> quickCodes a ((Block [])::cs)
| QPURE: #cs:codes -> r:range -> msg:string -> pre:((unit -> GTot Type0) -> GTot Type0) ->
    (unit -> PURE unit pre) -> quickCodes a cs -> quickCodes a cs
//| QBindPURE: #cs:codes -> b:Type -> r:range -> msg:string -> pre:((b -> GTot Type0) -> GTot Type0) ->
//    (unit -> PURE b pre) -> (va_state -> b -> GTot (quickCodes a cs)) -> quickCodes a ((Block [])::cs)
| QLemma: #cs:codes -> r:range -> msg:string -> pre:Type0 -> post:(squash pre -> Type0) ->
    (unit -> Lemma (requires pre) (ensures post ())) -> quickCodes a cs -> quickCodes a cs
| QGhost: #cs:codes -> b:Type -> r:range -> msg:string -> pre:Type0 -> post:(b -> Type0) ->
    (unit -> Ghost b (requires pre) (ensures post)) -> (b -> GTot (quickCodes a cs)) -> quickCodes a ((Block [])::cs)
| QAssertBy: #cs:codes -> r:range -> msg:string -> p:Type0 ->
    quickCodes unit [] -> quickCodes a cs -> quickCodes a cs

[@va_qattr] unfold let va_QBind (#a:Type0) (#b:Type) (#c:code) (#cs:codes) (r:range) (msg:string) (qc:quickCode b c) (qcs:va_state -> b -> GTot (quickCodes a cs)) : quickCodes a (c::cs) = QBind r msg qc qcs
[@va_qattr] unfold let va_QEmpty (#a:Type0) (v:a) : quickCodes a [] = QEmpty v
[@va_qattr] unfold let va_QLemma (#a:Type0) (#cs:codes) (r:range) (msg:string) (pre:Type0) (post:(squash pre -> Type0)) (l:unit -> Lemma (requires pre) (ensures post ())) (qcs:quickCodes a cs) : quickCodes a cs = QLemma r msg pre post l qcs
[@va_qattr] unfold let va_QSeq (#a:Type0) (#b:Type) (#c:code) (#cs:codes) (r:range) (msg:string) (qc:quickCode b c) (qcs:quickCodes a cs) : quickCodes a (c::cs) = QSeq r msg qc qcs

[@va_qattr]
let va_qPURE
    (#cs:codes) (#pre:(unit -> GTot Type0) -> GTot Type0) (#a:Type0) (r:range) (msg:string)
    ($l:unit -> PURE unit pre) (qcs:quickCodes a cs)
  : quickCodes a cs =
  QPURE r msg pre l qcs

(* REVIEW: this might be useful, but inference of pre doesn't work as well as for va_qPURE
  (need to provide pre explicitly; as a result, no need to put $ on l)
[@va_qattr]
let va_qBindPURE
    (#a #b:Type0) (#cs:codes) (pre:(b -> GTot Type0) -> GTot Type0) (r:range) (msg:string)
    (l:unit -> PURE b pre) (qcs:va_state -> b -> GTot (quickCodes a cs))
  : quickCodes a ((Block [])::cs) =
  QBindPURE b r msg pre l qcs
*)

[@va_qattr]
let wp_proc (#a:Type0) (c:code) (qc:quickCode a c) (s0:va_state) (k:va_state -> a -> Type0) : Type0 =
  match qc with
  | QProc _ _ wp _ -> wp s0 k

let wp_Seq_t (a:Type0) = va_state -> a -> Type0
let wp_Bind_t (a:Type0) = va_state -> a -> Type0
let k_AssertBy (p:Type0) (_:va_state) () = p

[@va_qattr]
let va_range1 = mk_range "" 0 0 0 0

val empty_list_is_small (#a:Type) (x:list a) : Lemma
  ([] #a == x \/ [] #a << x)

[@va_qattr]
let rec wp (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (mods:mods_t) (k:va_state -> a -> Type0) (s0:va_state) :
  Tot Type0 (decreases %[cs; 0; qcs])
  =
  match qcs with
  | QEmpty g -> k s0 g
  | QSeq r msg qc qcs ->
      let c::cs = cs in
      label r msg (mods_contains mods qc.mods /\ wp_proc c qc s0 (wp_Seq cs qcs mods k))
  | QBind r msg qc qcs ->
      let c::cs = cs in
      label r msg (mods_contains mods qc.mods /\ wp_proc c qc s0 (wp_Bind cs qcs mods k))
  | QGetState f ->
      let c::cs = cs in
      wp cs (f s0) mods k s0
  | QPURE r msg pre l qcs ->
      // REVIEW: rather than just applying 'pre' directly to k,
      // we define this in a roundabout way so that:
      // - it works even if 'pre' isn't known to be monotonic
      // - F*'s error reporting uses 'guard_free' to process labels inside (wp cs qcs mods k s0)
      (forall (p:unit -> GTot Type0).//{:pattern (pre p)}
        (forall (u:unit).{:pattern (guard_free (p u))} wp cs qcs mods k s0 ==> p ())
        ==>
        label r msg (pre p))
(*
  | QBindPURE b r msg pre l qcs ->
      let c::cs = cs in
      (forall (p:b -> GTot Type0).//{:pattern (pre p)}
        (forall (g:b).{:pattern (guard_free (p g))} wp cs (qcs s0 g) mods k s0 ==> p g)
        ==>
        label r msg (pre p))
*)
  | QLemma r msg pre post l qcs ->
      label r msg pre /\ (post () ==> wp cs qcs mods k s0)
  | QGhost b r msg pre post l qcs ->
      let c::cs = cs in
      label r msg pre /\ (forall (g:b). post g ==> wp cs (qcs g) mods k s0)
  | QAssertBy r msg p qcsBy qcs ->
      empty_list_is_small cs;
      wp [] qcsBy mods (k_AssertBy p) s0 /\ (p ==> wp cs qcs mods k s0)
// Hoist lambdas out of main definition to avoid issues with function equality
and wp_Seq (#a:Type0) (#b:Type0) (cs:codes) (qcs:quickCodes b cs) (mods:mods_t) (k:va_state -> b -> Type0) :
  Tot (wp_Seq_t a) (decreases %[cs; 1; qcs])
  =
  let f s0 _ = wp cs qcs mods k s0 in f
and wp_Bind (#a:Type0) (#b:Type0) (cs:codes) (qcs:va_state -> a -> GTot (quickCodes b cs)) (mods:mods_t) (k:va_state -> b -> Type0) :
  Tot (wp_Bind_t a) (decreases %[cs; 1; qcs])
  =
  let f s0 g = wp cs (qcs s0 g) mods k s0 in f

val wp_sound (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (mods:mods_t) (k:va_state -> a -> Type0) (s0:va_state)
  : Ghost (va_state & va_fuel & a)
  (requires t_require s0 /\ wp cs qcs mods k s0)
  (ensures fun (sN, fN, gN) ->
    eval (Block cs) s0 fN sN /\ update_state_mods mods sN s0 == sN /\ state_inv sN /\ k sN gN
  )

///// Block

unfold let block = va_Block

[@va_qattr]
let wp_block (#a:Type) (#cs:codes) (qcs:va_state -> GTot (quickCodes a cs)) (mods:mods_t) (s0:va_state) (k:va_state -> a -> Type0) : Type0 =
  wp cs (qcs s0) mods k s0

val qblock_proof (#a:Type) (#cs:codes) (qcs:va_state -> GTot (quickCodes a cs)) (mods:mods_t) (s0:va_state) (k:va_state -> a -> Type0)
  : Ghost (va_state & va_fuel & a)
  (requires t_require s0 /\ wp_block qcs mods s0 k)
  (ensures fun (sM, f0, g) ->
    eval_code (block cs) s0 f0 sM /\ update_state_mods mods sM s0 == sM /\ state_inv sM /\ k sM g
  )

[@"opaque_to_smt" va_qattr]
let qblock (#a:Type) (#cs:codes) (mods:mods_t) (qcs:va_state -> GTot (quickCodes a cs)) : quickCode a (block cs) =
  QProc (block cs) mods (wp_block qcs mods) (qblock_proof qcs mods)

///// If, InlineIf

[@va_qattr]
let wp_InlineIf (#a:Type) (#c1:code) (#c2:code) (b:bool) (qc1:quickCode a c1) (qc2:quickCode a c2) (mods:mods_t) (s0:va_state) (k:va_state -> a -> Type0) : Type0 =
  // REVIEW: this duplicates k
  (    b ==> mods_contains mods qc1.mods /\ QProc?.wp qc1 s0 k) /\
  (not b ==> mods_contains mods qc2.mods /\ QProc?.wp qc2 s0 k)

val qInlineIf_proof (#a:Type) (#c1:code) (#c2:code) (b:bool) (qc1:quickCode a c1) (qc2:quickCode a c2) (mods:mods_t) (s0:va_state) (k:va_state -> a -> Type0)
  : Ghost (va_state & va_fuel & a)
  (requires t_require s0 /\ wp_InlineIf b qc1 qc2 mods s0 k)
  (ensures fun (sM, f0, g) ->
    eval_code (if_code b c1 c2) s0 f0 sM /\ update_state_mods mods sM s0 == sM /\ state_inv sM /\ k sM g
  )

[@"opaque_to_smt" va_qattr]
let va_qInlineIf (#a:Type) (#c1:code) (#c2:code) (mods:mods_t) (b:bool) (qc1:quickCode a c1) (qc2:quickCode a c2) : quickCode a (if_code b c1 c2) =
  QProc (if_code b c1 c2) mods (wp_InlineIf b qc1 qc2 mods) (qInlineIf_proof b qc1 qc2 mods)

noeq type cmp =
| Cmp_eq : o1:va_operand{not (OMem? o1 || OStack? o1)} -> o2:va_operand{not (OMem? o2 || OStack? o2)} -> cmp
| Cmp_ne : o1:va_operand{not (OMem? o1 || OStack? o1)} -> o2:va_operand{not (OMem? o2 || OStack? o2)} -> cmp
| Cmp_le : o1:va_operand{not (OMem? o1 || OStack? o1)} -> o2:va_operand{not (OMem? o2 || OStack? o2)} -> cmp
| Cmp_ge : o1:va_operand{not (OMem? o1 || OStack? o1)} -> o2:va_operand{not (OMem? o2 || OStack? o2)} -> cmp
| Cmp_lt : o1:va_operand{not (OMem? o1 || OStack? o1)} -> o2:va_operand{not (OMem? o2 || OStack? o2)} -> cmp
| Cmp_gt : o1:va_operand{not (OMem? o1 || OStack? o1)} -> o2:va_operand{not (OMem? o2 || OStack? o2)} -> cmp

[@va_qattr]
let cmp_to_ocmp (c:cmp) : ocmp =
  match c with
  | Cmp_eq o1 o2 -> va_cmp_eq o1 o2
  | Cmp_ne o1 o2 -> va_cmp_ne o1 o2
  | Cmp_le o1 o2 -> va_cmp_le o1 o2
  | Cmp_ge o1 o2 -> va_cmp_ge o1 o2
  | Cmp_lt o1 o2 -> va_cmp_lt o1 o2
  | Cmp_gt o1 o2 -> va_cmp_gt o1 o2

[@va_qattr]
let valid_cmp (c:cmp) (s:va_state) : Type0 =
  match c with
  | Cmp_eq o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_ne o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_le o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_ge o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_lt o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_gt o1 o2 -> valid_operand o1 s /\ valid_operand o2 s

[@va_qattr]
let eval_cmp (s:va_state) (c:cmp) : GTot bool =
  match c with
  | Cmp_eq o1 o2 -> va_eval_opr64 s o1 =  va_eval_opr64 s o2
  | Cmp_ne o1 o2 -> va_eval_opr64 s o1 <> va_eval_opr64 s o2
  | Cmp_le o1 o2 -> va_eval_opr64 s o1 <= va_eval_opr64 s o2
  | Cmp_ge o1 o2 -> va_eval_opr64 s o1 >= va_eval_opr64 s o2
  | Cmp_lt o1 o2 -> va_eval_opr64 s o1 <  va_eval_opr64 s o2
  | Cmp_gt o1 o2 -> va_eval_opr64 s o1 >  va_eval_opr64 s o2

[@va_qattr]
let wp_If (#a:Type) (#c1:code) (#c2:code) (b:cmp) (qc1:quickCode a c1) (qc2:quickCode a c2) (mods:mods_t) (s0:va_state) (k:va_state -> a -> Type0) : Type0 =
  // REVIEW: this duplicates k
  valid_cmp b s0 /\
  (     eval_cmp s0 b  ==> mods_contains mods qc1.mods /\ QProc?.wp qc1 s0 k) /\
  (not (eval_cmp s0 b) ==> mods_contains mods qc2.mods /\ QProc?.wp qc2 s0 k)

val qIf_proof (#a:Type) (#c1:code) (#c2:code) (b:cmp) (qc1:quickCode a c1) (qc2:quickCode a c2) (mods:mods_t) (s0:va_state) (k:va_state -> a -> Type0)
  : Ghost (va_state & va_fuel & a)
  (requires t_require s0 /\ wp_If b qc1 qc2 mods s0 k)
  (ensures fun (sM, f0, g) ->
    eval_code (IfElse (cmp_to_ocmp b) c1 c2) s0 f0 sM /\ update_state_mods mods sM s0 == sM /\ state_inv sM /\ k sM g
  )

[@"opaque_to_smt" va_qattr]
let va_qIf (#a:Type) (#c1:code) (#c2:code) (mods:mods_t) (b:cmp) (qc1:quickCode a c1) (qc2:quickCode a c2) : quickCode a (IfElse (cmp_to_ocmp b) c1 c2) =
  QProc (IfElse (cmp_to_ocmp b) c1 c2) mods (wp_If b qc1 qc2 mods) (qIf_proof b qc1 qc2 mods)

///// While

[@va_qattr]
let wp_While_inv
    (#a #d:Type) (#c:code) (qc:a -> quickCode a c) (mods:mods_t) (inv:va_state -> a -> Type0)
    (dec:va_state -> a -> d) (s1:va_state) (g1:a) (s2:va_state) (g2:a)
    : Type0 =
  s2.vs_ok /\ inv s2 g2 /\ mods_contains mods (qc g2).mods /\ dec s2 g2 << dec s1 g1

[@va_qattr]
let wp_While_body
    (#a #d:Type) (#c:code) (b:cmp) (qc:a -> quickCode a c) (mods:mods_t) (inv:va_state -> a -> Type0)
    (dec:va_state -> a -> d) (g1:a) (s1:va_state) (k:va_state -> a -> Type0)
    : Type0 =
  valid_cmp b s1 /\
  (     eval_cmp s1 b  ==> mods_contains mods (qc g1).mods /\ QProc?.wp (qc g1) s1 (wp_While_inv qc mods inv dec s1 g1)) /\
  (not (eval_cmp s1 b) ==> k s1 g1)

[@va_qattr]
let wp_While
    (#a #d:Type) (#c:code) (b:cmp) (qc:a -> quickCode a c) (mods:mods_t) (inv:va_state -> a -> Type0)
    (dec:va_state -> a -> d) (g0:a) (s0:va_state) (k:va_state -> a -> Type0)
    : Type0 =
  inv s0 g0 /\ mods_contains mods (qc g0).mods /\
  // REVIEW: we could get a better WP with forall (...state components...) instead of forall (s1:va_state)
  (forall (s1:va_state) (g1:a). inv s1 g1 ==> wp_While_body b qc mods inv dec g1 s1 k)

val qWhile_proof
    (#a #d:Type) (#c:code) (b:cmp) (qc:a -> quickCode a c) (mods:mods_t) (inv:va_state -> a -> Type0)
    (dec:va_state -> a -> d) (g0:a) (s0:va_state) (k:va_state -> a -> Type0)
  : Ghost (va_state & va_fuel & a)
  (requires t_require s0 /\ wp_While b qc mods inv dec g0 s0 k)
  (ensures fun (sM, f0, g) ->
    eval_code (While (cmp_to_ocmp b) c) s0 f0 sM /\ update_state_mods mods sM s0 == sM /\ state_inv sM /\ k sM g
  )

[@"opaque_to_smt" va_qattr]
let va_qWhile
    (#a #d:Type) (#c:code) (mods:mods_t) (b:cmp) (qc:a -> quickCode a c) (inv:va_state -> a -> Type0)
    (dec:va_state -> a -> d) (g0:a)
  : quickCode a (While (cmp_to_ocmp b) c) =
  QProc (While (cmp_to_ocmp b) c) mods (wp_While b qc mods inv dec g0)
    (qWhile_proof b qc mods inv dec g0)

///// Assert, Assume, AssertBy

let tAssertLemma (p:Type0) = unit -> Lemma (requires p) (ensures p)
val qAssertLemma (p:Type0) : tAssertLemma p

[@va_qattr]
let va_qAssert (#a:Type) (#cs:codes) (r:range) (msg:string) (e:Type0) (qcs:quickCodes a cs) : quickCodes a cs =
  QLemma r msg e (fun () -> e) (qAssertLemma e) qcs

let tAssumeLemma (p:Type0) = unit -> Lemma (requires True) (ensures p)
val qAssumeLemma (p:Type0) : tAssumeLemma p

[@va_qattr]
let va_qAssume (#a:Type) (#cs:codes) (r:range) (msg:string) (e:Type0) (qcs:quickCodes a cs) : quickCodes a cs =
  QLemma r msg True (fun () -> e) (qAssumeLemma e) qcs

let tAssertSquashLemma (p:Type0) = unit -> Ghost (squash p) (requires p) (ensures fun () -> p)
val qAssertSquashLemma (p:Type0) : tAssertSquashLemma p

[@va_qattr]
let va_qAssertSquash
    (#a:Type) (#cs:codes) (r:range) (msg:string) (e:Type0) (qcs:squash e -> GTot (quickCodes a cs))
  : quickCodes a ((Block [])::cs) =
  QGhost (squash e) r msg e (fun () -> e) (qAssertSquashLemma e) qcs

//let tAssertByLemma (#a:Type) (p:Type0) (qcs:quickCodes a []) (mods:mods_t) (s0:state) =
//  unit -> Lemma (requires t_require s0 /\ wp [] qcs mods (fun _ _ -> p) s0) (ensures p)
//val qAssertByLemma (#a:Type) (p:Type0) (qcs:quickCodes a []) (mods:mods_t) (s0:state) : tAssertByLemma p qcs mods s0
//
//[@va_qattr]
//let va_qAssertBy (#a:Type) (#cs:codes) (mods:mods_t) (r:range) (msg:string) (p:Type0) (qcsBy:quickCodes unit []) (s0:state) (qcsTail:quickCodes a cs) : quickCodes a cs =
//  QLemma r msg (t_require s0 /\ wp [] qcsBy mods (fun _ _ -> p) s0) (fun () -> p) (qAssertByLemma p qcsBy mods s0) qcsTail

[@va_qattr]
let va_qAssertBy (#a:Type) (#cs:codes) (r:range) (msg:string) (p:Type0) (qcsBy:quickCodes unit []) (qcsTail:quickCodes a cs) : quickCodes a cs =
  QAssertBy r msg p qcsBy qcsTail

///// Code

val wp_sound_code (#a:Type0) (c:code) (qc:quickCode a c) (k:va_state -> a -> Type0) (s0:va_state) :
  Ghost (va_state & fuel & a)
  (requires t_require s0 /\ QProc?.wp qc s0 k)
  (ensures fun (sN, fN, gN) -> eval_code c s0 fN sN /\ update_state_mods qc.mods sN s0 == sN /\ state_inv sN /\ k sN gN)

[@va_qattr]
let rec regs_match_file (r0:Regs.t) (r1:Regs.t) (rf:reg_file_id) (k:nat{k <= n_regs rf}) : Type0 =
  if k = 0 then True
  else
    let r = Reg rf (k - 1) in
    Regs.sel r r0 == Regs.sel r r1 /\ regs_match_file r0 r1 rf (k - 1)

[@va_qattr]
let rec regs_match (r0:Regs.t) (r1:Regs.t) (k:nat{k <= n_reg_files}) : Type0 =
  if k = 0 then True
  else regs_match_file r0 r1 (k - 1) (n_regs (k - 1)) /\ regs_match r0 r1 (k - 1)

[@va_qattr]
let all_regs_match (r0:Regs.t) (r1:Regs.t) : Type0 =
  regs_match r0 r1 n_reg_files

[@va_qattr]
let state_match (s0:va_state) (s1:va_state) : Type0 =
  s0.vs_ok == s1.vs_ok /\
  all_regs_match s0.vs_regs s1.vs_regs /\
  s0.vs_flags == s1.vs_flags /\
  s0.vs_heap == s1.vs_heap /\
  s0.vs_stack == s1.vs_stack /\
  s0.vs_stackTaint == s1.vs_stackTaint

val lemma_state_match (s0:va_state) (s1:va_state) : Lemma
  (requires state_match s0 s1)
  (ensures state_eq s0 s1)

[@va_qattr]
let va_state_match (s0:va_state) (s1:va_state) : Pure Type0
  (requires True)
  (ensures fun b -> b ==> state_eq s0 s1)
  =
  FStar.Classical.move_requires (lemma_state_match s0) s1;
  state_match s0 s1

[@va_qattr]
unfold let wp_sound_code_pre (#a:Type0) (#c:code) (qc:quickCode a c) (s0:va_state) (k:(s0':va_state{s0 == s0'}) -> va_state -> a -> Type0) : Type0 =
  forall
      (ok:bool)
      (regs:Regs.t)
      (flags:Flags.t)
      //(mem:vale_full_heap) // splitting mem into its components makes the VCs slightly cleaner:
      (mem_layout:vale_heap_layout)
      (mem_heap:vale_heap)
      (mem_heaplets:vale_heaplets)
      (stack:vale_stack)
      (stackTaint:memtaint)
      .
    let mem = {
      vf_layout = mem_layout;
      vf_heap = mem_heap;
      vf_heaplets = mem_heaplets;
    } in
    let s0' = {
      vs_ok = ok;
      vs_regs = regs;
      vs_flags = flags;
      vs_heap = mem;
      vs_stack = stack;
      vs_stackTaint = stackTaint
    } in
    s0 == s0' ==> QProc?.wp qc (state_eta s0') (k (state_eta s0'))

unfold let wp_sound_code_post (#a:Type0) (#c:code) (qc:quickCode a c) (s0:va_state) (k:(s0':va_state{s0 == s0'}) -> va_state -> a -> Type0) ((sN:va_state), (fN:fuel), (gN:a)) : Type0 =
  eval c s0 fN sN /\
  update_state_mods qc.mods sN s0 == sN /\
  state_inv sN /\
  k s0 sN gN

unfold let normal_steps : list string =
  [
    `%Mkvale_state?.vs_ok;
    `%Mkvale_state?.vs_regs;
    `%Mkvale_state?.vs_flags;
    `%Mkvale_state?.vs_heap;
    `%Mkvale_state?.vs_stack;
    `%Mkvale_state?.vs_stackTaint;
    `%Mkvale_full_heap?.vf_layout;
    `%Mkvale_full_heap?.vf_heap;
    `%Mkvale_full_heap?.vf_heaplets;
    `%QProc?.wp;
    `%QProc?.mods;
    `%OConst?;
    `%OReg?;
    `%OMem?;
    `%OStack?;
    `%FStar.FunctionalExtensionality.on_dom;
  ]

unfold let normal (x:Type0) : Type0 = norm [iota; zeta; simplify; primops; delta_attr [`%va_qattr]; delta_only normal_steps] x

val va_wp_sound_code_norm (#a:Type0) (c:code) (qc:quickCode a c) (s0:va_state) (k:(s0':va_state{s0 == s0'}) -> va_state -> a -> Type0) :
  Ghost (va_state & fuel & a)
    (t_require s0 /\ normal (wp_sound_code_pre qc s0 k))
    (wp_sound_code_post qc s0 k)

