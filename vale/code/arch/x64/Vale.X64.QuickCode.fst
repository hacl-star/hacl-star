module Vale.X64.QuickCode
open FStar.Mul
open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.Arch.HeapImpl
open Vale.X64.State
open Vale.X64.Decls

irreducible let qmodattr = ()

type mod_t =
| Mod_None : mod_t
| Mod_ok: mod_t
| Mod_reg: reg -> mod_t
| Mod_flags: mod_t
| Mod_mem: mod_t
| Mod_mem_layout: mod_t
| Mod_mem_heaplet: heaplet_id -> mod_t
| Mod_stack: mod_t
| Mod_stackTaint: mod_t
unfold let mods_t = list mod_t
unfold let va_mods_t = mods_t

[@va_qattr] unfold let va_Mod_None = Mod_None
[@va_qattr] unfold let va_Mod_ok = Mod_ok
[@va_qattr] unfold let va_Mod_reg64 (r:reg_64) = Mod_reg (Reg 0 r)
[@va_qattr] unfold let va_Mod_xmm (r:reg_xmm) = Mod_reg (Reg 1 r)
[@va_qattr] unfold let va_Mod_flags = Mod_flags
[@va_qattr] unfold let va_Mod_mem = Mod_mem
[@va_qattr] unfold let va_Mod_mem_layout = Mod_mem_layout
[@va_qattr] unfold let va_Mod_mem_heaplet (n:heaplet_id) = Mod_mem_heaplet n
[@va_qattr] unfold let va_Mod_stack = Mod_stack
[@va_qattr] unfold let va_Mod_stackTaint = Mod_stackTaint

[@va_qattr "opaque_to_smt"]
let mod_eq (x y:mod_t) : Pure bool (requires True) (ensures fun b -> b == (x = y)) =
  match x with
  | Mod_None -> (match y with Mod_None -> true | _ -> false)
  | Mod_ok -> (match y with Mod_ok -> true | _ -> false)
  | Mod_reg rx -> (match y with Mod_reg ry -> rx = ry | _ -> false)
  | Mod_flags -> (match y with Mod_flags -> true | _ -> false)
  | Mod_mem -> (match y with Mod_mem -> true | _ -> false)
  | Mod_mem_layout -> (match y with Mod_mem_layout -> true | _ -> false)
  | Mod_mem_heaplet nx -> (match y with Mod_mem_heaplet ny -> nx = ny | _ -> false)
  | Mod_stack -> (match y with Mod_stack -> true | _ -> false)
  | Mod_stackTaint -> (match y with Mod_stackTaint -> true | _ -> false)

[@va_qattr]
let update_state_mod (m:mod_t) (sM sK:vale_state) : vale_state =
  match m with
  | Mod_None -> sK
  | Mod_ok -> va_update_ok sM sK
  | Mod_reg r -> va_update_reg r sM sK
  | Mod_flags -> va_update_flags sM sK
  | Mod_mem -> va_update_mem sM sK
  | Mod_mem_layout -> va_update_mem_layout sM sK
  | Mod_mem_heaplet n -> va_update_mem_heaplet n sM sK
  | Mod_stack -> va_update_stack sM sK
  | Mod_stackTaint -> va_update_stackTaint sM sK

[@va_qattr]
let rec update_state_mods (mods:mods_t) (sM sK:vale_state) : vale_state =
  match mods with
  | [] -> sK
  | m::mods -> update_state_mod m sM (update_state_mods mods sM sK)

[@va_qattr]
unfold let update_state_mods_norm (mods:mods_t) (sM sK:vale_state) : vale_state =
  norm [iota; zeta; delta_attr [`%qmodattr]; delta_only [`%update_state_mods; `%update_state_mod]] (update_state_mods mods sM sK)

let va_lemma_norm_mods (mods:mods_t) (sM sK:vale_state) : Lemma
  (ensures update_state_mods mods sM sK == update_state_mods_norm mods sM sK)
  = ()

[@va_qattr qmodattr]
let va_mod_dst_opr64 (o:va_operand) : mod_t =
  match o with
  | OConst n -> Mod_None
  | OReg r -> Mod_reg (Reg 0 r)
  | OMem _ -> Mod_None // TODO: support destination memory operands
  | OStack _ -> Mod_None // TODO: support destination stack operands

[@va_qattr qmodattr]
let va_mod_reg_opr64 (o:va_reg_operand) : mod_t =
  match o with
  | OReg r -> Mod_reg (Reg 0 r)

[@va_qattr qmodattr] let va_mod_xmm (x:reg_xmm) : mod_t = Mod_reg (Reg 1 x)
[@va_qattr qmodattr] let va_mod_heaplet (h:heaplet_id) : mod_t = Mod_mem_heaplet h

let quickProc_wp (a:Type0) : Type u#1 = (s0:vale_state) -> (wp_continue:vale_state -> a -> Type0) -> Type0

let k_true (#a:Type0) (_:vale_state) (_:a) = True

let t_monotone (#a:Type0) (c:va_code) (wp:quickProc_wp a) : Type =
  s0:vale_state -> k1:(vale_state -> a -> Type0) -> k2:(vale_state -> a -> Type0) -> Lemma
    (requires (forall (s:vale_state) (g:a). k1 s g ==> k2 s g))
    (ensures wp s0 k1 ==> wp s0 k2)

let t_compute (#a:Type0) (c:va_code) (wp:quickProc_wp a) : Type =
  s0:vale_state -> Ghost (vale_state & va_fuel & a)
    (requires wp s0 k_true)
    (ensures fun _ -> True)

let t_require (s0:va_state) = state_inv s0
unfold let va_t_require = t_require

let va_t_ensure (#a:Type0) (c:va_code) (mods:mods_t) (s0:vale_state) (k:(vale_state -> a -> Type0)) =
  fun (sM, f0, g) -> eval_code c s0 f0 sM /\ update_state_mods mods sM s0 == sM /\ state_inv sM /\ k sM g

let t_proof (#a:Type0) (c:va_code) (mods:mods_t) (wp:quickProc_wp a) : Type =
  s0:vale_state -> k:(vale_state -> a -> Type0) -> Ghost (vale_state & va_fuel & a)
    (requires t_require s0 /\ wp s0 k)
    (ensures va_t_ensure c mods s0 k)

// Code that returns a ghost value of type a
[@va_qattr]
noeq type quickCode (a:Type0) : va_code -> Type =
| QProc:
    c:va_code ->
    mods:mods_t ->
    wp:quickProc_wp a ->
    proof:t_proof c mods wp ->
    quickCode a c

[@va_qattr]
unfold let va_quickCode = quickCode

[@va_qattr]
unfold let va_QProc = QProc
