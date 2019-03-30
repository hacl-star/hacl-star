module X64.Vale.QuickCode
open Prop_s
open X64.Machine_s
open X64.Vale.State
open X64.Vale.Decls

irreducible let qmodattr = ()

type mod_t =
| Mod_None : mod_t
| Mod_ok: mod_t
| Mod_reg: reg -> mod_t
| Mod_xmm: xmm -> mod_t
| Mod_flags: mod_t
| Mod_mem: mod_t
| Mod_stack: mod_t
| Mod_memTaint: mod_t
unfold let mods_t = list mod_t

[@va_qattr "opaque_to_smt"]
let mod_eq (x y:mod_t) : Pure bool (requires True) (ensures fun b -> b == (x = y)) =
  match x with
  | Mod_None -> (match y with Mod_None -> true | _ -> false)
  | Mod_ok -> (match y with Mod_ok -> true | _ -> false)
  | Mod_reg rx -> (match y with Mod_reg ry -> rx = ry | _ -> false)
  | Mod_xmm xx -> (match y with Mod_xmm xy -> xx = xy | _ -> false)
  | Mod_flags -> (match y with Mod_flags -> true | _ -> false)
  | Mod_mem -> (match y with Mod_mem -> true | _ -> false)
  | Mod_stack -> (match y with Mod_stack -> true | _ -> false)
  | Mod_memTaint -> (match y with Mod_memTaint -> true | _ -> false)

[@va_qattr]
let update_state_mod (m:mod_t) (sM sK:state) : state =
  match m with
  | Mod_None -> sK
  | Mod_ok -> va_update_ok sM sK
  | Mod_reg r -> va_update_reg r sM sK
  | Mod_xmm x -> va_update_xmm x sM sK
  | Mod_flags -> va_update_flags sM sK
  | Mod_mem -> va_update_mem sM sK
  | Mod_stack -> va_update_stack sM sK
  | Mod_memTaint -> va_update_memTaint sM sK

[@va_qattr]
let rec update_state_mods (mods:mods_t) (sM sK:state) : state =
  match mods with
  | [] -> sK
  | m::mods -> update_state_mod m sM (update_state_mods mods sM sK)

[@va_qattr]
unfold let update_state_mods_norm (mods:mods_t) (sM sK:state) : state =
  norm [iota; zeta; delta_attr [`%qmodattr]; delta_only [`%update_state_mods; `%update_state_mod]] (update_state_mods mods sM sK)

let lemma_norm_mods (mods:mods_t) (sM sK:state) : Lemma
  (ensures update_state_mods mods sM sK == update_state_mods_norm mods sM sK)
  = ()

[@va_qattr qmodattr]
let va_mod_dst_opr64 (o:va_operand) : mod_t =
  match o with
  | TConst n -> Mod_None
  | TReg r -> Mod_reg r
  | TMem _ _ -> Mod_None // TODO: support destination memory operands
  | TStack _ -> Mod_None // TODO: support destination stack operands

[@va_qattr qmodattr]
let va_mod_reg_opr64 (o:va_reg_operand) : mod_t =
  match o with
  | TReg r -> Mod_reg r

[@va_qattr qmodattr] let va_mod_xmm (x:xmm) : mod_t = Mod_xmm x

let quickProc_wp (a:Type0) : Type u#1 = (s0:state) -> (wp_continue:state -> a -> Type0) -> Type0

let k_true (#a:Type0) (_:state) (_:a) = True

let t_monotone (#a:Type0) (c:va_code) (wp:quickProc_wp a) : Type =
  s0:state -> k1:(state -> a -> Type0) -> k2:(state -> a -> Type0) -> Lemma
    (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
    (ensures wp s0 k1 ==> wp s0 k2)

let t_compute (#a:Type0) (c:va_code) (wp:quickProc_wp a) : Type =
  s0:state -> Ghost (state * va_fuel * a)
    (requires wp s0 k_true)
    (ensures fun _ -> True)

let t_ensure (#a:Type0) (c:va_code) (mods:mods_t) (wp:quickProc_wp a) (monotone:t_monotone c wp) (compute:t_compute c wp) (s0:state) (k:(state -> a -> Type0){wp s0 k}) =
  monotone s0 k k_true;
  let (sM, f0, g) = compute s0 in
  eval_code c s0 f0 sM /\ update_state_mods mods sM s0 == sM /\ k sM g

let t_proof (#a:Type0) (c:va_code) (mods:mods_t) (wp:quickProc_wp a) (monotone:t_monotone c wp) (compute:t_compute c wp) : Type =
  s0:state -> k:(state -> a -> Type0) -> Lemma
    (requires wp s0 k)
    (ensures t_ensure c mods wp monotone compute s0 k)

// Code that returns a ghost value of type a
[@va_qattr]
noeq type quickCode (a:Type0) : va_code -> Type =
| QProc:
    c:va_code ->
    mods:mods_t ->
    wp:quickProc_wp a ->
    monotone:t_monotone c wp ->
    compute:t_compute c wp ->
    proof:t_proof c mods wp monotone compute ->
    quickCode a c

unfold let va_quickCode = quickCode
[@va_qattr]
unfold let va_QProc = QProc
