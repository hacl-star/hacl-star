module X64.Vale.QuickCode
open X64.Machine_s
open X64.Vale.State
open X64.Vale.Decls

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

let t_ensure (#a:Type0) (c:va_code) (wp:quickProc_wp a) (monotone:t_monotone c wp) (compute:t_compute c wp) (s0:state) (k:(state -> a -> Type0){wp s0 k}) =
  monotone s0 k k_true; let (sM, f0, g) = compute s0 in eval_code c s0 f0 sM /\ k sM g

let t_proof (#a:Type0) (c:va_code) (wp:quickProc_wp a) (monotone:t_monotone c wp) (compute:t_compute c wp) : Type =
  s0:state -> k:(state -> a -> Type0) -> Lemma
    (requires wp s0 k)
    (ensures t_ensure c wp monotone compute s0 k)

// Code that returns a ghost value of type a
[@va_qattr]
noeq type quickCode (a:Type0) : va_code -> Type =
| QProc:
    c:va_code ->
    wp:quickProc_wp a ->
    monotone:t_monotone c wp ->
    compute:t_compute c wp ->
    proof:t_proof c wp monotone compute ->
    quickCode a c

unfold let va_quickCode = quickCode
[@va_qattr]
unfold let va_QProc = QProc
