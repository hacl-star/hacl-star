module Vale.PPC64LE.Semantics_s

open FStar.Mul
open Vale.PPC64LE.Machine_s
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
include Vale.Arch.MachineHeap_s
open Vale.Arch.HeapTypes_s
open Vale.Arch.Heap
open Vale.Arch.Types
open Vale.Def.Sel
open Vale.SHA2.Wrapper

let (.[]) = Map.sel
let (.[]<-) = Map.upd

type ins =
  | Move         : dst:reg -> src:reg -> ins
  | Load64       : dst:reg -> base:reg -> offset:int -> ins
  | Store64      : src:reg -> base:reg -> offset:int -> ins
  | LoadImm64    : dst:reg -> src:simm16 -> ins
  | AddLa        : dst:reg -> src1:reg -> src2:simm16 -> ins
  | Add          : dst:reg -> src1:reg -> src2:reg -> ins
  | AddImm       : dst:reg -> src1:reg -> src2:simm16 -> ins
  | AddExtended  : dst:reg -> src1:reg -> src2:reg -> ins
  | AddExtendedOV: dst:reg -> src1:reg -> src2:reg -> ins
  | Sub          : dst:reg -> src1:reg -> src2:reg -> ins
  | SubImm       : dst:reg -> src1:reg -> src2:nsimm16 -> ins
  | MulLow64     : dst:reg -> src1:reg -> src2:reg -> ins
  | MulHigh64U   : dst:reg -> src1:reg -> src2:reg -> ins
  | Xor          : dst:reg -> src1:reg -> src2:reg -> ins
  | And          : dst:reg -> src1:reg -> src2:reg -> ins
  | Sr64Imm      : dst:reg -> src1:reg -> src2:bits64 -> ins
  | Sl64Imm      : dst:reg -> src1:reg -> src2:bits64 -> ins
  | Mfvsrd       : dst:reg -> src:vec -> ins
  | Mfvsrld      : dst:reg -> src:vec -> ins
  | Mtvsrdd      : dst:vec -> src1:reg -> src2:reg -> ins
  | Vadduwm      : dst:vec -> src1:vec -> src2:vec -> ins
  | Vxor         : dst:vec -> src1:vec -> src2:vec -> ins
  | Vslw         : dst:vec -> src1:vec -> src2:vec -> ins
  | Vsrw         : dst:vec -> src1:vec -> src2:vec -> ins
  | Vcmpequw     : dst:vec -> src1:vec -> src2:vec -> ins
  | Vsldoi       : dst:vec -> src1:vec -> src2:vec -> count:quad32bytes -> ins
  | Vmrghw       : dst:vec -> src1:vec -> src2:vec -> ins
  | Xxmrghd      : dst:vec -> src1:vec -> src2:vec -> ins
  | Vsel         : dst:vec -> src1:vec -> src2:vec -> sel:vec -> ins
  | Load128      : dst:vec -> base:reg -> offset:reg -> ins
  | Store128     : src:vec -> base:reg -> offset:reg -> ins
  | Load128Word4 : dst:vec -> base:reg -> offset:reg -> ins
  | Store128Word4: src:vec -> base:reg -> offset:reg -> ins
  | Load128Byte16: dst:vec -> base:reg -> offset:reg -> ins
  | Store128Byte16: src:vec -> base:reg -> offset:reg -> ins
  | Vshasigmaw0  : dst:vec -> src:vec -> ins
  | Vshasigmaw1  : dst:vec -> src:vec -> ins
  | Vshasigmaw2  : dst:vec -> src:vec -> ins
  | Vshasigmaw3  : dst:vec -> src:vec -> ins
  | Alloc        : n:nat64 -> ins
  | Dealloc      : n:nat64 -> ins
  | StoreStack128: src:vec -> t:taint -> offset:int -> ins
  | LoadStack128 : dst:vec -> t:taint -> offset:int -> ins
  | Ghost        : (_:unit) -> ins

type ocmp =
  | OEq: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | ONe: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | OLe: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | OGe: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | OLt: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | OGt: o1:cmp_opr -> o2:cmp_opr -> ocmp

type code = precode ins ocmp
type codes = list code

unfold let eval_reg (r:reg) (s:state) : nat64 = s.regs r
unfold let eval_vec (v:vec) (s:state) : quad32 = s.vecs v
unfold let eval_mem (ptr:int) (s:state) : nat64 = get_heap_val64 ptr (heap_get s.ms_heap)
unfold let eval_mem128 (ptr:int) (s:state) : quad32 = get_heap_val128 ptr (heap_get s.ms_heap)

unfold let eval_stack (ptr:int) (s:machine_stack) : nat64 =
  let Machine_stack _ mem = s in
  get_heap_val64 ptr mem
unfold let eval_stack128 (ptr:int) (s:machine_stack) : quad32 =
  let Machine_stack _ mem = s in
  get_heap_val128 ptr mem

(*
Check if the taint annotation of a memory operand matches the taint in the memory map.
Evaluation will fail in case of a mismatch.
This allows the taint analysis to learn information about the memory map from the annotation,
assuming that the code has been verified not to fail.
(Note that this only relates to memory maps, so non-memory operands need no annotation.)
*)
[@"opaque_to_smt"]
let rec match_n (addr:int) (n:nat) (memTaint:memTaint_t) (t:taint)
  : Tot (b:bool{b <==>
      (forall i.{:pattern (memTaint `Map.sel` i)}
        (i >= addr /\ i < addr + n) ==> memTaint.[i] == t)})
    (decreases n)
  =
  if n = 0 then true
  else if memTaint.[addr] <> t then false
  else match_n (addr + 1) (n - 1) memTaint t

[@"opaque_to_smt"]
let rec update_n (addr:int) (n:nat) (memTaint:memTaint_t) (t:taint)
  : Tot (m:memTaint_t{(
      forall i.{:pattern (m `Map.sel` i)}
        ((i >= addr /\ i < addr + n) ==> m.[i] == t) /\
        ((i < addr \/ i >= addr + n) ==> m.[i] == memTaint.[i]))})
    (decreases n)
  =
  if n = 0 then memTaint
  else update_n (addr + 1) (n - 1) (memTaint.[addr] <- t) t

let lemma_is_machine_heap_update64 (ptr:int) (v:nat64) (mh:machine_heap) : Lemma
  (requires valid_addr64 ptr mh)
  (ensures is_machine_heap_update mh (update_heap64 ptr v mh))
  [SMTPat (is_machine_heap_update mh (update_heap64 ptr v mh))]
  =
  reveal_opaque (`%valid_addr64) valid_addr64;
  update_heap64_reveal ();
  ()

let update_mem_and_taint (ptr:int) (v:nat64) (s:state) (t:taint) : state =
  if valid_addr64 ptr (heap_get s.ms_heap) then
    { s with
      ms_heap = heap_upd s.ms_heap
        (update_heap64 ptr v (heap_get s.ms_heap))
        (update_n ptr 8 (heap_taint s.ms_heap) t)
    }
  else s

let update_mem (ptr:int) (v:nat64) (s:state) : state =
  if valid_addr64 ptr (heap_get s.ms_heap) then
    { s with
      ms_heap = heap_upd s.ms_heap
        (update_heap64 ptr v (heap_get s.ms_heap))
        (heap_taint s.ms_heap)
    }
  else s

let lemma_is_machine_heap_update128 (ptr:int) (v:quad32) (mh:machine_heap) : Lemma
  (requires valid_addr128 ptr mh)
  (ensures is_machine_heap_update mh (update_heap128 ptr v mh))
  [SMTPat (is_machine_heap_update mh (update_heap128 ptr v mh))]
  =
  reveal_opaque (`%valid_addr128) valid_addr128;
  update_heap32_reveal ();
  update_heap128_reveal ();
  ()

let update_mem128 (ptr:int) (v:quad32) (s:state) : state =
  if valid_addr128 ptr (heap_get s.ms_heap) then
    { s with
      ms_heap = heap_upd s.ms_heap
        (update_heap128 ptr v (heap_get s.ms_heap))
        (heap_taint s.ms_heap)
    }
  else s

let update_mem128_and_taint (ptr:int) (v:quad32) (s:state) (t:taint) : state =
  if valid_addr128 ptr (heap_get s.ms_heap) then
    { s with
      ms_heap = heap_upd s.ms_heap
        (update_heap128 ptr v (heap_get s.ms_heap))
        (update_n ptr 16 (heap_taint s.ms_heap) t)
    }
  else s

unfold
let update_stack64' (ptr:int) (v:nat64) (s:machine_stack) : machine_stack =
  let Machine_stack init_r1 mem = s in
  let mem = update_heap64 ptr v mem in
  Machine_stack init_r1 mem

unfold
let update_stack128' (ptr:int) (v:quad32) (s:machine_stack) : machine_stack =
  let Machine_stack init_r1 mem = s in
  let mem = update_heap128 ptr v mem in
  Machine_stack init_r1 mem

let update_stack_and_taint (ptr:int) (v:nat64) (s:state) (t:taint) : state =
  let Machine_stack init_r1 mem = s.ms_stack in
  { s with
    ms_stack = update_stack64' ptr v s.ms_stack;
    ms_stackTaint = update_n ptr 8 s.ms_stackTaint t;
  }

let update_stack128_and_taint (ptr:int) (v:quad32) (s:state) (t:taint) : state =
  let Machine_stack init_r1 mem = s.ms_stack in
  { s with
    ms_stack = update_stack128' ptr v s.ms_stack;
    ms_stackTaint = update_n ptr 16 s.ms_stackTaint t
  }

unfold
let valid_src_stack64 (ptr:int) (st:machine_stack) : bool =
  let Machine_stack init_r1 mem = st in
  valid_addr64 ptr mem

unfold
let valid_src_stack128 (ptr:int) (st:machine_stack) : bool =
  let Machine_stack init_r1 mem = st in
  valid_addr128 ptr mem

unfold
let valid_src_stack64_and_taint (ptr:int) (s:state) (t:taint) : bool =
  valid_src_stack64 ptr s.ms_stack && match_n ptr 8 s.ms_stackTaint t

unfold
let valid_src_stack128_and_taint (ptr:int) (s:state) (t:taint) : bool =
  valid_src_stack128 ptr s.ms_stack && match_n ptr 16 s.ms_stackTaint t

let valid_src_stack (r:reg) (s:state) : bool =
  valid_src_stack64 (eval_reg r s) s.ms_stack

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  eval_reg m.address s + m.offset

let eval_cmp_opr (o:cmp_opr) (s:state) : nat64 =
  match o with
  | CReg r -> eval_reg r s
  | CImm n -> int_to_nat64 n

let eval_ocmp (s:state) (c:ocmp) :bool =
  match c with
  | OEq o1 o2 -> eval_cmp_opr o1 s = eval_cmp_opr o2 s
  | ONe o1 o2 -> eval_cmp_opr o1 s <> eval_cmp_opr o2 s
  | OLe o1 o2 -> eval_cmp_opr o1 s <= eval_cmp_opr o2 s
  | OGe o1 o2 -> eval_cmp_opr o1 s >= eval_cmp_opr o2 s
  | OLt o1 o2 -> eval_cmp_opr o1 s < eval_cmp_opr o2 s
  | OGt o1 o2 -> eval_cmp_opr o1 s > eval_cmp_opr o2 s

let eval_cmp_cr0 (s:state) (c:ocmp) : cr0_t =
  match c with
  | OEq o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | ONe o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | OLe o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | OGe o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | OLt o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | OGt o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)

unfold
let valid_dst_stack64 (r1:nat64) (ptr:int) (st:machine_stack) : bool =
  let Machine_stack init_r1 mem = st in
    // We are allowed to store anywhere between rRsp and the initial stack pointer
  ptr >= r1 && ptr + 8 <= init_r1

unfold
let valid_dst_stack128 (r1:nat64) (ptr:int) (st:machine_stack) : bool =
  let Machine_stack init_r1 mem = st in
    // We are allowed to store anywhere between rRsp and the initial stack pointer
    ptr >= r1 && ptr + 16 <= init_r1

let valid_dst_stack64_addr (m:maddr) (s:state) : bool =
  valid_dst_stack64 (eval_reg 1 s) (eval_maddr m s) s.ms_stack

let valid_dst_stack128_addr (m:maddr) (s:state) : bool =
  valid_dst_stack128 (eval_reg 1 s) (eval_maddr m s) s.ms_stack

let update_reg' (r:reg) (v:nat64) (s:state) : state =
  { s with regs = regs_make (fun (r':reg) -> if r' = r then v else s.regs r') }

let update_vec' (vr:vec) (v:quad32) (s:state) : state =
  { s with vecs = vecs_make (fun (vr':vec) -> if vr' = vr then v else s.vecs vr') }

let update_r1' (new_r1:int) (s:state) : state =
  let Machine_stack init_r1 mem = s.ms_stack in
  // Only modify the stack pointer if the new value is valid, that is in the current stack frame, and in the same page
  if new_r1 >= init_r1 - 65536 && new_r1 <= init_r1 then
    update_reg' 1 new_r1 s
  else
    s

let free_stack' (start finish:int) (st:machine_stack) : machine_stack =
  let Machine_stack init_r1 mem = st in
  let domain = Map.domain mem in
  // Returns the domain, without elements between start and finish
  let restricted_domain = Vale.Lib.Set.remove_between domain start finish in
  // The new domain of the stack does not contain elements between start and finish
  let new_mem = Map.restrict restricted_domain mem in
  Machine_stack init_r1 new_mem

let valid_mem (m:maddr) (s:state) : bool =
  valid_maddr_offset64 m.offset && valid_addr64 (eval_maddr m s) (heap_get s.ms_heap)

let valid_mem128 (r:reg) (i:reg) (s:state) : bool =
  valid_addr128 (eval_reg r s + eval_reg i s) (heap_get s.ms_heap)

let valid_mem128' (m:maddr) (s:state) : bool =
  valid_maddr_offset128 m.offset && valid_addr128 (eval_maddr m s) (heap_get s.ms_heap)

let valid_mem_and_taint (m:maddr) (t:taint) (s:state) : bool =
  let ptr = eval_maddr m s in
  valid_maddr_offset64 m.offset && valid_addr64 ptr (heap_get s.ms_heap) && match_n ptr 8 (heap_taint s.ms_heap) t

let valid_mem128_and_taint (m:maddr) (s:state) (t:taint) : bool =
  let ptr = eval_maddr m s in
  valid_addr128 ptr (heap_get s.ms_heap) && match_n ptr 16 (heap_taint s.ms_heap) t

let valid_ocmp (c:ocmp) (s:state) : bool =
  match c with
  | OEq o1 _ -> valid_first_cmp_opr o1
  | ONe o1 _ -> valid_first_cmp_opr o1
  | OLe o1 _ -> valid_first_cmp_opr o1
  | OGe o1 _ -> valid_first_cmp_opr o1
  | OLt o1 _ -> valid_first_cmp_opr o1
  | OGt o1 _ -> valid_first_cmp_opr o1

let xer_ov (xer:xer_t) : bool =
  xer.ov

let xer_ca (xer:xer_t) : bool =
  xer.ca

let update_xer_ov (xer:xer_t) (new_xer_ov:bool) : (new_xer:xer_t{xer_ov new_xer == new_xer_ov}) =
  { xer with ov = new_xer_ov }

let update_xer_ca (xer:xer_t) (new_xer_ca:bool) : (new_xer:xer_t{xer_ca new_xer == new_xer_ca}) =
  { xer with ca = new_xer_ca }

// Define a stateful monad to simplify defining the instruction semantics
let st (a:Type) = state -> a & state

unfold
let return (#a:Type) (x:a) :st a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok=s0.ok && s1.ok && s2.ok}

unfold
let get :st state =
  fun s -> s, s

unfold
let set (s:state) :st unit =
  fun _ -> (), s

unfold
let fail :st unit =
  fun s -> (), {s with ok=false}

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : state = snd (f s)

let update_reg (r:reg) (v:nat64) :st unit =
  s <-- get;
  set (update_reg' r v s)

let update_vec (vr:vec) (v:quad32) :st unit =
  s <-- get;
  set (update_vec' vr v s)

let update_xer (new_xer:xer_t) :st unit =
  s <-- get;
  set ( { s with xer = new_xer } )

let update_cr0 (new_cr0:cr0_t) :st unit =
  s <-- get;
  set ( { s with cr0 = new_cr0 } )

unfold
let update_r1 (i:int) : st unit =
  // Only modify the stack pointer if the new value is valid, that is in the current stack frame, and in the same page
 check (fun s -> i >= s.ms_stack.initial_r1 - 65536);;
 check (fun s -> i <= s.ms_stack.initial_r1);;
 s <-- get;
 set (update_r1' i s)

let free_stack (start finish:int) : st unit =
  s <-- get;
  set ( { s with ms_stack = free_stack' start finish s.ms_stack} )

// Core definition of instruction semantics
let eval_ins (ins:ins) : st unit =
  s <-- get;
  match ins with
  | Move dst src ->
    update_reg dst (eval_reg src s)

  | Load64 dst base offset ->
    check (valid_mem ({ address=base; offset=offset }));;
    update_reg dst (eval_mem (eval_reg base s + offset) s)

  | Store64 src base offset ->
    check (valid_mem ({ address=base; offset=offset }));;
    set (update_mem (eval_reg base s + offset) (eval_reg src s) s)

  | LoadImm64 dst src ->
    update_reg dst (int_to_nat64 src)

  | AddLa dst src1 src2 ->
    update_reg dst ((eval_reg src1 s + src2) % pow2_64)

  | Add dst src1 src2 ->
    update_reg dst ((eval_reg src1 s + eval_reg src2 s) % pow2_64)

  | AddImm dst src1 src2 ->
    update_reg dst ((eval_reg src1 s + int_to_nat64 src2) % pow2_64)

  | AddExtended dst src1 src2 ->
    let old_carry = if xer_ca(s.xer) then 1 else 0 in
    let sum = (eval_reg src1 s) + (eval_reg src2 s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_reg dst (sum % pow2_64);;
    update_xer (update_xer_ca s.xer new_carry)

  | AddExtendedOV dst src1 src2 ->
    let old_carry = if xer_ov(s.xer) then 1 else 0 in
    let sum = (eval_reg src1 s) + (eval_reg src2 s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_reg dst (sum % pow2_64);;
    update_xer (update_xer_ov s.xer new_carry)

  | Sub dst src1 src2 ->
    update_reg dst ((eval_reg src1 s - eval_reg src2 s) % pow2_64)

  | SubImm dst src1 src2 ->
    update_reg dst ((eval_reg src1 s - int_to_nat64 src2) % pow2_64)
  
  | MulLow64 dst src1 src2 ->
    update_reg dst ((eval_reg src1 s * eval_reg src2 s) % pow2_64)

  | MulHigh64U dst src1 src2 ->
    update_reg dst (FStar.UInt.mul_div #64 (eval_reg src1 s) (eval_reg src2 s))
  
  | Xor dst src1 src2 ->
    update_reg dst (ixor (eval_reg src1 s) (eval_reg src2 s))
  
  | And dst src1 src2 ->
    update_reg dst (iand (eval_reg src1 s) (eval_reg src2 s))
  
  | Sr64Imm dst src1 src2 ->
    update_reg dst (ishr (eval_reg src1 s) src2)
  
  | Sl64Imm dst src1 src2 ->
    update_reg dst (ishl (eval_reg src1 s) src2)
  
  | Mfvsrd dst src ->
    let src_q = eval_vec src s in
    let src_two = four_to_two_two src_q in
    let extracted_nat64 = two_to_nat 32 (two_select src_two 1) in
    update_reg dst extracted_nat64
  
  | Mfvsrld dst src ->
    let src_q = eval_vec src s in
    let src_two = four_to_two_two src_q in
    let extracted_nat64 = two_to_nat 32 (two_select src_two 0) in
    update_reg dst extracted_nat64

  | Mtvsrdd dst src1 src2 ->
    let val_src1 = eval_reg src1 s in
    let val_src2 = eval_reg src2 s in
    update_vec dst (Mkfour
      (val_src2 % pow2_32)
      (val_src2 / pow2_32)
      (val_src1 % pow2_32)
      (val_src1 / pow2_32))
  
  | Vadduwm dst src1 src2 ->
    update_vec dst (add_wrap_quad32 (eval_vec src1 s) (eval_vec src2 s))
  
  | Vxor dst src1 src2 ->
    update_vec dst (quad32_xor (eval_vec src1 s) (eval_vec src2 s))
  
  | Vslw dst src1 src2 ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    update_vec dst (Mkfour
      (ishl src1_q.lo0 (src2_q.lo0 % 32))
      (ishl src1_q.lo1 (src2_q.lo1 % 32))
      (ishl src1_q.hi2 (src2_q.hi2 % 32))
      (ishl src1_q.hi3 (src2_q.hi3 % 32)))

  | Vsrw dst src1 src2 ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    update_vec dst (Mkfour
      (ishr src1_q.lo0 (src2_q.lo0 % 32))
      (ishr src1_q.lo1 (src2_q.lo1 % 32))
      (ishr src1_q.hi2 (src2_q.hi2 % 32))
      (ishr src1_q.hi3 (src2_q.hi3 % 32)))

  | Vcmpequw dst src1 src2 ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    let eq_result (b:bool):nat32 = if b then 0xFFFFFFFF else 0 in
    let eq_val = Mkfour
      (eq_result (src1_q.lo0 = src2_q.lo0))
      (eq_result (src1_q.lo1 = src2_q.lo1))
      (eq_result (src1_q.hi2 = src2_q.hi2))
      (eq_result (src1_q.hi3 = src2_q.hi3))
    in
    update_vec dst eq_val
  
  | Vsldoi dst src1 src2 count ->
    check (fun s -> (count = 4 || count = 8 || count = 12));;  // We only spec the one very special case we need
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    if count = 4 then update_vec dst (Mkfour src2_q.hi3 src1_q.lo0 src1_q.lo1 src1_q.hi2)
    else if count = 8 then update_vec dst (Mkfour src2_q.hi2 src2_q.hi3 src1_q.lo0 src1_q.lo1)
    else if count = 12 then update_vec dst (Mkfour src2_q.lo1 src2_q.hi2 src2_q.hi3 src1_q.lo0)
    else fail

  | Vmrghw dst src1 src2 ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    update_vec dst (Mkfour src2_q.lo1 src1_q.lo1 src2_q.hi3 src1_q.hi3)

  | Xxmrghd dst src1 src2 ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    update_vec dst (Mkfour src2_q.hi2 src2_q.hi3 src1_q.hi2 src1_q.hi3)
  
  | Vsel dst src1 src2 sel ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    let sel_q = eval_vec sel s in
    update_vec dst (Mkfour
      (isel32 src2_q.lo0 src1_q.lo0 sel_q.lo0)
      (isel32 src2_q.lo1 src1_q.lo1 sel_q.lo1)
      (isel32 src2_q.hi2 src1_q.hi2 sel_q.hi2)
      (isel32 src2_q.hi3 src1_q.hi3 sel_q.hi3))

  | Load128 dst base offset ->
    check (valid_mem128 base offset);;
    update_vec dst (eval_mem128 (eval_reg base s + eval_reg offset s) s)
  
  | Store128 src base offset ->
    check (valid_mem128 base offset);;
    set (update_mem128 (eval_reg base s + eval_reg offset s) (eval_vec src s) s)
  
  | Load128Word4 dst base offset ->
    check (valid_mem128 base offset);;
    let src_q = eval_mem128 (eval_reg base s + eval_reg offset s) s in
    update_vec dst (Mkfour src_q.hi3 src_q.hi2 src_q.lo1 src_q.lo0)

  | Store128Word4 src base offset ->
    check (valid_mem128 base offset);;
    let src_q = eval_vec src s in
    set (update_mem128 (eval_reg base s + eval_reg offset s) (Mkfour src_q.hi3 src_q.hi2 src_q.lo1 src_q.lo0) s)

  | Load128Byte16 dst base offset ->
    check (valid_mem128 base offset);;
    update_vec dst (reverse_bytes_quad32 (eval_mem128 (eval_reg base s + eval_reg offset s) s))
  
  | Store128Byte16 src base offset ->
    check (valid_mem128 base offset);;
    set (update_mem128 (eval_reg base s + eval_reg offset s) (reverse_bytes_quad32 (eval_vec src s)) s)
  
  | Vshasigmaw0 dst src ->
    let src_q = eval_vec src s in
    update_vec dst (Mkfour
      (sigma256_0_0 src_q.lo0)
      (sigma256_0_0 src_q.lo1)
      (sigma256_0_0 src_q.hi2)
      (sigma256_0_0 src_q.hi3))

  | Vshasigmaw1 dst src ->
    let src_q = eval_vec src s in
    update_vec dst (Mkfour
      (sigma256_0_1 src_q.lo0)
      (sigma256_0_1 src_q.lo1)
      (sigma256_0_1 src_q.hi2)
      (sigma256_0_1 src_q.hi3))
  
  | Vshasigmaw2 dst src ->
    let src_q = eval_vec src s in
    update_vec dst (Mkfour
      (sigma256_1_0 src_q.lo0)
      (sigma256_1_0 src_q.lo1)
      (sigma256_1_0 src_q.hi2)
      (sigma256_1_0 src_q.hi3))
  
  | Vshasigmaw3 dst src ->
    let src_q = eval_vec src s in
    update_vec dst (Mkfour
      (sigma256_1_1 src_q.lo0)
      (sigma256_1_1 src_q.lo1)
      (sigma256_1_1 src_q.hi2)
      (sigma256_1_1 src_q.hi3))
  
  | Alloc n ->
    check (fun s -> n % 16 = 0);;
    update_r1 (eval_reg 1 s - n)

  | Dealloc n ->
    let old_r1 = eval_reg 1 s in
    let new_r1 = old_r1 + n in
    update_r1 new_r1;;
    // The deallocated stack memory should now be considered invalid
    free_stack old_r1 new_r1

  | StoreStack128 src t offset ->
    check (fun s -> valid_maddr_offset128 offset);;
    let r1_pos = eval_reg 1 s + offset in
    check (fun s -> r1_pos <= s.ms_stack.initial_r1 - 16);;
    set (update_stack128_and_taint r1_pos (eval_vec src s) s t)

  | LoadStack128 dst t offset ->
    check (fun s -> valid_maddr_offset128 offset);;
    let r1_pos = eval_reg 1 s + offset in
    check (fun s -> r1_pos + 16 <= s.ms_stack.initial_r1);;
    check (fun s -> valid_src_stack128_and_taint r1_pos s t);;
    update_vec dst (eval_stack128 r1_pos s.ms_stack)

  | Ghost _ ->
    set s

let run_ocmp (s:state) (c:ocmp) : state & bool =
  let s = run (check (valid_ocmp c)) s in
  ({s with cr0 = eval_cmp_cr0 s c}, eval_ocmp s c)

(*
 * These functions return an option state
 * None case arises when the while loop runs out of fuel
 *)
let rec eval_code (c:code) (fuel:nat) (s:state) : Tot (option state) (decreases %[fuel; c]) =
  match c with
  | Ins ins ->
    Some (run (eval_ins ins) s)
  | Block l ->
    eval_codes l fuel s
  | IfElse cond ifTrue ifFalse  ->
    let (s, b) = run_ocmp s cond in
    if b then eval_code ifTrue fuel s else eval_code ifFalse fuel s
  | While b c ->
    eval_while b c fuel s
and eval_codes (l:codes) (fuel:nat) (s:state) : Tot (option state) (decreases %[fuel; l]) =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c fuel s in
    if None? s_opt then None else eval_codes tl fuel (Some?.v s_opt)
and eval_while (cond:ocmp) (c:code) (fuel:nat) (s0:state) : Tot (option state) (decreases %[fuel; c]) =
  if fuel = 0 then None else
  let (s0, b) = run_ocmp s0 cond in
  if not b then Some s0
  else
    match eval_code c (fuel - 1) s0 with
    | None -> None
    | Some s1 ->
      if s1.ok then eval_while cond c (fuel - 1) s1  // success: continue to next iteration
      else Some s1  // failure: propagate failure immediately
