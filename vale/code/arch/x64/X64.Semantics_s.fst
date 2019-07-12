module X64.Semantics_s

open X64.Machine_s
open X64.Memory_s
open Words_s
open Words.Two_s
open Words.Four_s
open Types_s
open FStar.Seq.Base
module S = X64.Bytes_Semantics_s

type uint64 = UInt64.t

type ins = S.ins

type ocmp = S.ocmp

type code = S.code
type codes = S.codes

//let u (i:int{FStar.UInt.fits i 64}) : uint64 = FStar.UInt64.uint_to_t i
//let v (u:uint64) : nat64 = FStar.UInt64.v u

val havoc : state -> ins -> nat64
let havoc s ins = S.havoc s.state ins

// TODO: Need to be sure that load/store_mem does an appropriate little-endian load

unfold let eval_reg (r:reg) (s:state) : nat64 = S.eval_reg r s.state
unfold let eval_xmm (i:xmm) (s:state) : quad32 = S.eval_xmm i s.state

unfold let eval_mem (ptr:int) (s:state) : GTot nat64 = load_mem64 ptr s.mem
unfold let eval_mem128 (ptr:int) (s:state) : GTot quad32 = load_mem128 ptr s.mem

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> (eval_reg reg s) + offset
    | MIndex base scale index offset -> (eval_reg base s) + scale * (eval_reg index s) + offset

let eval_operand (o:operand) (s:state) : GTot nat64 =
  match o with
  | OConst n -> int_to_nat64 n
  | OReg r -> eval_reg r s
  | OMem m -> eval_mem (eval_maddr m s) s

let eval_mov128_op (o:mov128_op) (s:state) : GTot quad32 =
  match o with
  | Mov128Xmm i -> eval_xmm i s
  | Mov128Mem m -> eval_mem128 (eval_maddr m s) s

let eval_ocmp (s:state) (c:ocmp) : GTot bool =
  match c with
  | S.OEq o1 o2 -> eval_operand o1 s = eval_operand o2 s
  | S.ONe o1 o2 -> eval_operand o1 s <> eval_operand o2 s
  | S.OLe o1 o2 -> eval_operand o1 s <= eval_operand o2 s
  | S.OGe o1 o2 -> eval_operand o1 s >= eval_operand o2 s
  | S.OLt o1 o2 -> eval_operand o1 s < eval_operand o2 s
  | S.OGt o1 o2 -> eval_operand o1 s > eval_operand o2 s

let update_reg' (r:reg) (v:nat64) (s:state) : state = {s with state = S.update_reg' r v s.state}

let update_xmm' (x:xmm) (v:quad32) (s:state) : state = {s with state = S.update_xmm' x v s.state}

let update_mem (ptr:int) (v:nat64) (s:state) : GTot state =
  let s' = { state = if valid_mem64 ptr s.mem then S.update_mem ptr v s.state
  else s.state; mem = store_mem64 ptr v s.mem } in
  valid_state_store_mem64 ptr v s;
  s'

let update_mem128 (ptr:int) (v:quad32) (s:state) : GTot state =
  let s' = { state = if valid_mem128 ptr s.mem then S.update_mem128 ptr v s.state
    else s.state ; mem = store_mem128 ptr v s.mem } in
 valid_state_store_mem128 ptr v s;
 s'

let valid_maddr (m:maddr) (s:state) : GTot bool =
  valid_mem64 (eval_maddr m s) s.mem

let valid_maddr128 (m:maddr) (s:state) : GTot bool =
  valid_mem128 (eval_maddr m s) s.mem

let valid_operand (o:operand) (s:state) : GTot bool =
  match o with
  | OConst n -> true
  | OReg r -> true
  | OMem m -> valid_maddr m s

let valid_mov128_op (o:mov128_op) (s:state) : GTot bool =
  match o with
  | Mov128Xmm i -> true (* We leave it to the printer/assembler to object to invalid XMM indices *)
  | Mov128Mem m -> valid_maddr128 m s

let valid_shift_operand (o:operand) (s:state) : GTot bool =
  valid_operand o s && (eval_operand o s) < 64

let valid_ocmp (c:ocmp) (s:state) : GTot bool =
  match c with
  | S.OEq o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | S.ONe o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | S.OLe o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | S.OGe o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | S.OLt o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | S.OGt o1 o2 -> valid_operand o1 s && valid_operand o2 s

let valid_dst_operand (o:operand) (s:state) : GTot bool =
  valid_operand o s && valid_dst o

let update_operand_preserve_flags' (o:operand) (v:nat64) (s:state) : GTot state =
  match o with
  | OConst _ -> {s with state = {s.state with S.ok = false}}
  | OReg r -> update_reg' r v s
  | OMem m -> update_mem (eval_maddr m s) v s // see valid_maddr for how eval_maddr connects to b and i

let update_mov128_op_preserve_flags' (o:mov128_op) (v:quad32) (s:state) : GTot state =
  match o with
  | Mov128Xmm i -> update_xmm' i v s
  | Mov128Mem m -> update_mem128 (eval_maddr m s) v s

// Default version havocs flags
let update_operand' (o:operand) (ins:ins) (v:nat64) (s:state) : GTot state =
  let s' = update_operand_preserve_flags' o v s in
  { s' with state = {s'.state with S.flags = havoc s ins } }

(* REVIEW: Will we regret exposing a mod here?  Should flags be something with more structure? *)
let cf (flags:nat64) : bool =
  flags % 2 = 1

//unfold let bit11 = normalize_term (pow2 11)
let _ = assert (2048 == normalize_term (pow2 11))

let overflow(flags:nat64) : bool =
  (flags / 2048) % 2 = 1  // OF is the 12th bit, so dividing by 2^11 shifts right 11 bits

let update_cf (flags:nat64) (new_cf:bool) : (new_flags:nat64{cf new_flags == new_cf}) =
  if new_cf then
    if not (cf flags) then
      flags + 1
    else
      flags
  else
    if (cf flags) then
      flags - 1
    else
      flags

let update_of (flags:nat64) (new_of:bool) : (new_flags:nat64{overflow new_flags == new_of}) =
  if new_of then
    if not (overflow flags) then
      flags + 2048
    else
      flags
  else
    if (overflow flags) then
      flags - 2048
    else
      flags

(* Define a stateful monad to simplify defining the instruction semantics *)
let st (a:Type) = state -> GTot (a * state)

unfold
let return (#a:Type) (x:a) : GTot (st a) =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> GTot (st b)) :GTot (st b) =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with state = {s2.state with S.ok=s0.state.S.ok && s1.state.S.ok && s2.state.S.ok} }

unfold
let get : st state =
  fun s -> s, s

unfold
let set (s:state) : GTot (st unit) =
  fun _ -> (), s

unfold
let fail : (st unit) =
  fun s -> (), {s with state = {s.state with S.ok=false} }

unfold
let check_imm (valid:bool) : GTot (st unit) =
  if valid then
    return ()
  else
    fail

unfold
let check (valid: state -> GTot bool) : GTot (st unit) =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : GTot state = snd (f s)

(* Monadic update operations *)
unfold
let update_operand_preserve_flags (dst:operand) (v:nat64) :GTot (st unit) =
  check (valid_dst_operand dst);;
  s <-- get;
  set (update_operand_preserve_flags' dst v s)

unfold
let update_mov128_op_preserve_flags (dst:mov128_op) (v:quad32) : GTot (st unit) =
  check (valid_mov128_op dst);;
  s <-- get;
  set (update_mov128_op_preserve_flags' dst v s)

// Default version havocs flags
unfold
let update_operand (dst:operand) (ins:ins) (v:nat64) :GTot (st unit) =
  check (valid_dst_operand dst);;
  s <-- get;
  set (update_operand' dst ins v s)

let update_reg (r:reg) (v:nat64) : GTot (st unit) =
  s <-- get;
  set (update_reg' r v s)

let update_xmm (x:xmm)  (ins:ins) (v:quad32) : GTot (st unit) =
  s <-- get;
  let s' = update_xmm' x v s in
  set (  { s' with state = {s'.state with S.flags = havoc s ins } } )

let update_xmm_preserve_flags (x:xmm) (v:quad32) : GTot (st unit) =
  s <-- get;
  set ( update_xmm' x v s )

let update_flags (new_flags:nat64) : GTot (st unit) =
  s <-- get;
  set ( { s with state = {s.state with S.flags = new_flags } } )

let update_cf_of (new_cf new_of:bool) : GTot (st unit) =
  s <-- get;
  set ( { s with state = {s.state with S.flags = update_cf (update_of s.state.S.flags new_of) new_cf } } )

(* Core definition of instruction semantics *)
let eval_ins (ins:ins) : GTot (st unit) =
  s <-- get;
  match ins with
  | S.Mov64 dst src ->
    check (valid_operand src);;
    update_operand_preserve_flags dst (eval_operand src s)

  | S.Add64 dst src ->
    check (valid_operand src);;
    let sum = (eval_operand dst s) + (eval_operand src s) in
    let new_carry = sum >= pow2_64 in
    update_operand dst ins ((eval_operand dst s + eval_operand src s) % pow2_64);;
    update_flags (update_cf s.state.S.flags new_carry)

  | S.AddLea64 dst src1 src2 ->
    check (valid_operand src1);;
    check (valid_operand src2);;
    update_operand_preserve_flags dst ((eval_operand src1 s + eval_operand src2 s) % pow2_64)

  | S.AddCarry64 dst src ->
    check (valid_operand src);;
    let old_carry = if cf(s.state.S.flags) then 1 else 0 in
    let sum = (eval_operand dst s) + (eval_operand src s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_operand dst ins (sum % pow2_64);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.state.S.flags new_carry)  // We specify cf, but underspecify everything else

  | S.Adcx64 dst src ->
    check (valid_operand src);;
    let old_carry = if cf(s.state.S.flags) then 1 else 0 in
    let sum = (eval_operand dst s) + (eval_operand src s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_operand dst ins (sum % pow2_64);;
    update_flags (update_cf s.state.S.flags new_carry)  // Explicitly touches only CF

  | S.Adox64 dst src ->
    check (valid_operand src);;
    let old_carry = if overflow(s.state.S.flags) then 1 else 0 in
    let sum = (eval_operand dst s) + (eval_operand src s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_operand dst ins (sum % pow2_64);;
    update_flags (update_of s.state.S.flags new_carry)  // Explicitly touches only OF

  | S.Sub64 dst src ->
    check (valid_operand src);;
    update_operand dst ins ((eval_operand dst s - eval_operand src s) % pow2_64)

  | S.Mul64 src ->
    check (valid_operand src);;
    let hi = FStar.UInt.mul_div #64 (eval_reg Rax s) (eval_operand src s) in
    let lo = FStar.UInt.mul_mod #64 (eval_reg Rax s) (eval_operand src s) in
    update_reg Rax lo;;
    update_reg Rdx hi;;
    update_flags (havoc s ins)

  | S.Mulx64 dst_hi dst_lo src ->
    check (valid_operand src);;
    let hi = FStar.UInt.mul_div #64 (eval_reg Rdx s) (eval_operand src s) in
    let lo = FStar.UInt.mul_mod #64 (eval_reg Rdx s) (eval_operand src s) in
    update_operand_preserve_flags dst_lo lo;;
    update_operand_preserve_flags dst_hi hi

  | S.IMul64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (FStar.UInt.mul_mod #64 (eval_operand dst s) (eval_operand src s))

  | S.Xor64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (Types_s.ixor (eval_operand dst s) (eval_operand src s));;
    update_cf_of false false

  | S.And64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (Types_s.iand (eval_operand dst s) (eval_operand src s))

  | S.Shr64 dst amt ->
    check (valid_shift_operand amt);;
    update_operand dst ins (Types_s.ishr (eval_operand dst s) (eval_operand amt s))

  | S.Shl64 dst amt ->
    check (valid_shift_operand amt);;
    update_operand dst ins (Types_s.ishl (eval_operand dst s) (eval_operand amt s))

  | S.Push src ->
    check (valid_operand src);;
    let new_rsp = ((eval_reg Rsp s) - 8) % pow2_64 in
    update_operand_preserve_flags (OMem (MConst new_rsp)) (eval_operand src s);;
    update_reg Rsp new_rsp

  | S.Pop dst ->
    let stack_val = OMem (MReg Rsp 0) in
    check (valid_operand stack_val);;
    let new_dst = eval_operand stack_val s in
    let new_rsp = ((eval_reg Rsp s) + 8) % pow2_64 in
    update_operand_preserve_flags dst new_dst;;
    update_reg Rsp new_rsp

  // In the XMM-related instructions below, we generally don't need to check for validity of the operands,
  // since all possibilities are valid, thanks to dependent types

  | S.Paddd dst src ->
    let src_q = eval_xmm src s in
    let dst_q = eval_xmm dst s in
    update_xmm dst ins (Mkfour ((dst_q.lo0 + src_q.lo0) % pow2_32)
                               ((dst_q.lo1 + src_q.lo1) % pow2_32)
                               ((dst_q.hi2 + src_q.hi2) % pow2_32)
                               ((dst_q.hi3 + src_q.hi3) % pow2_32))

  | S.Pxor dst src ->
    update_xmm_preserve_flags dst (quad32_xor (eval_xmm dst s) (eval_xmm src s))

  | S.Pslld dst amt ->
    check_imm (0 <= amt && amt < 32);;
    update_xmm_preserve_flags dst (four_map (fun i -> ishl i amt) (eval_xmm dst s))

  | S.Psrld dst amt ->
    check_imm (0 <= amt && amt < 32);;
    update_xmm_preserve_flags dst (four_map (fun i -> ishr i amt) (eval_xmm dst s))

  | S.Psrldq dst amt ->
    check_imm (0 <= amt && amt < 16);;
    let src_q = eval_xmm dst s in
    let src_bytes = le_quad32_to_bytes src_q in
    let abs_amt = if 0 <= amt && amt <= (length src_bytes) then amt else 0 in // F* can't use the check_imm above
    let zero_pad = Seq.create abs_amt 0 in
    let remaining_bytes = slice src_bytes abs_amt (length src_bytes) in
    let dst_q = le_bytes_to_quad32 (append zero_pad remaining_bytes) in
    update_xmm_preserve_flags dst dst_q

  | S.Shufpd dst src permutation ->
    check_imm (0 <= permutation && permutation < 4);;
    let src_q = eval_xmm src s in
    let dst_q = eval_xmm dst s in
    let result = Mkfour (if permutation % 2 = 0 then dst_q.lo0 else dst_q.hi2)
                        (if permutation % 2 = 0 then dst_q.lo1 else dst_q.hi3)
                        (if (permutation / 2) % 2 = 0 then src_q.lo0 else src_q.hi2)
                        (if (permutation / 2) % 2 = 0 then src_q.lo1 else src_q.hi3) in
    update_xmm dst ins result

  | S.Pshufb dst src ->
    let src_q = eval_xmm src s in
    let dst_q = eval_xmm dst s in
    // We only spec a restricted version sufficient for a handful of standard patterns
    check_imm (S.is_full_byte_reversal_mask src_q || S.is_high_dup_reversal_mask src_q || S.is_lower_upper_byte_reversal_mask src_q);;
    if S.is_full_byte_reversal_mask src_q then
      update_xmm dst ins (reverse_bytes_quad32 dst_q)
    else if S.is_high_dup_reversal_mask src_q then
      update_xmm dst ins (Mkfour (reverse_bytes_nat32 dst_q.hi3)
                                 (reverse_bytes_nat32 dst_q.hi2)
                                 (reverse_bytes_nat32 dst_q.hi3)
                                 (reverse_bytes_nat32 dst_q.hi2))
    else if S.is_lower_upper_byte_reversal_mask src_q then
      update_xmm dst ins (Mkfour (reverse_bytes_nat32 dst_q.lo1)
                                 (reverse_bytes_nat32 dst_q.lo0)
                                 (reverse_bytes_nat32 dst_q.hi3)
                                 (reverse_bytes_nat32 dst_q.hi2))
    else fail

  | S.Pshufd dst src permutation ->
    let bits:bits_of_byte = byte_to_twobits permutation in
    let src_val = eval_xmm src s in
    let permuted_xmm = Mkfour
         (select_word src_val bits.lo0)
         (select_word src_val bits.lo1)
         (select_word src_val bits.hi2)
         (select_word src_val bits.hi3)
    in
    update_xmm_preserve_flags dst permuted_xmm

  | S.Pcmpeqd dst src ->
    let src_q = eval_xmm src s in
    let dst_q = eval_xmm dst s in
    let eq_result (b:bool):nat32 = if b then 0xFFFFFFFF else 0 in
    let eq_val = Mkfour
        (eq_result (src_q.lo0 = dst_q.lo0))
        (eq_result (src_q.lo1 = dst_q.lo1))
        (eq_result (src_q.hi2 = dst_q.hi2))
        (eq_result (src_q.hi3 = dst_q.hi3))
    in
    update_xmm_preserve_flags dst eq_val

  | S.Pextrq dst src index ->
    let src_q = eval_xmm src s in
    let src_two = four_to_two_two src_q in
    let extracted_nat64 = two_to_nat 32 (two_select src_two (index % 2)) in
    update_operand_preserve_flags dst extracted_nat64

  | S.Pinsrd dst src index ->
    check (valid_operand src);;
    let dst_q = eval_xmm dst s in
    update_xmm_preserve_flags dst  (insert_nat32 dst_q ((eval_operand src s) % pow2_32) (index % 4))

  | S.Pinsrq dst src index ->
    check (valid_operand src);;
    let dst_q = eval_xmm dst s in
    update_xmm_preserve_flags dst (insert_nat64 dst_q (eval_operand src s) (index % 2))

  | S.VPSLLDQ dst src count ->
    check (fun s -> count = 4);;  // We only spec the one very special case we need
    let src_q = eval_xmm src s in
    let shifted_xmm = Mkfour 0 src_q.lo0 src_q.lo1 src_q.hi2 in
    update_xmm_preserve_flags dst shifted_xmm

  | S.MOVDQU dst src ->
    check (valid_mov128_op src);;
    update_mov128_op_preserve_flags dst (eval_mov128_op src s)

  | S.Pclmulqdq dst src imm ->
    (
      let Mkfour a0 a1 a2 a3 = eval_xmm dst s in
      let Mkfour b0 b1 b2 b3 = eval_xmm src s in
      let f x0 x1 y0 y1 =
        let x = Math.Poly2.Bits_s.of_double32 (Mktwo x0 x1) in
        let y = Math.Poly2.Bits_s.of_double32 (Mktwo y0 y1) in
        update_xmm dst ins (Math.Poly2.Bits_s.to_quad32 (Math.Poly2_s.mul x y))
        in
      match imm with
      | 0 -> f a0 a1 b0 b1
      | 1 -> f a2 a3 b0 b1
      | 16 -> f a0 a1 b2 b3
      | 17 -> f a2 a3 b2 b3
      | _ -> fail
    )

  | S.AESNI_enc dst src ->
    let dst_q = eval_xmm dst s in
    let src_q = eval_xmm src s in
    update_xmm dst ins (quad32_xor (AES_s.mix_columns_LE (AES_s.sub_bytes (AES_s.shift_rows_LE dst_q))) src_q)

  | S.AESNI_enc_last dst src ->
    let dst_q = eval_xmm dst s in
    let src_q = eval_xmm src s in
    update_xmm dst ins (quad32_xor (AES_s.sub_bytes (AES_s.shift_rows_LE dst_q)) src_q)

  | S.AESNI_dec dst src ->
    let dst_q = eval_xmm dst s in
    let src_q = eval_xmm src s in
    update_xmm dst ins (quad32_xor (AES_s.inv_mix_columns_LE (AES_s.inv_sub_bytes (AES_s.inv_shift_rows_LE dst_q))) src_q)

  | S.AESNI_dec_last dst src ->
    let dst_q = eval_xmm dst s in
    let src_q = eval_xmm src s in
    update_xmm dst ins (quad32_xor (AES_s.inv_sub_bytes (AES_s.inv_shift_rows_LE dst_q)) src_q)

  | S.AESNI_imc dst src ->
    let src_q = eval_xmm src s in
    update_xmm dst ins (AES_s.inv_mix_columns_LE src_q)

  | S.AESNI_keygen_assist dst src imm ->
    let src_q = eval_xmm src s in
    update_xmm dst ins (Mkfour (AES_s.sub_word src_q.lo1)
                               (ixor (AES_s.rot_word_LE (AES_s.sub_word src_q.lo1)) imm)
                               (AES_s.sub_word src_q.hi3)
                               (ixor (AES_s.rot_word_LE (AES_s.sub_word src_q.hi3)) imm))


(*
 * These functions return an option state
 * None case arises when the while loop runs out of fuel
 *)
// TODO: IfElse and While should havoc the flags
val eval_code:  c:code           -> fuel:nat -> s:state -> GTot (option state) (decreases %[fuel; c])
val eval_codes: l:codes          -> fuel:nat -> s:state -> GTot (option state) (decreases %[fuel; l])
val eval_while: b:ocmp -> c:code -> fuel:nat -> s:state -> GTot (option state) (decreases %[fuel; c])

let rec eval_code c fuel s =
  match c with
  | Ins ins                       -> Some (run (eval_ins ins) s)
  | Block l                       -> eval_codes l fuel s
  | IfElse ifCond ifTrue ifFalse  -> let s = run (check (valid_ocmp ifCond)) s in
           if eval_ocmp s ifCond then eval_code ifTrue fuel s else eval_code ifFalse fuel s
  | While b c                     -> eval_while b c fuel s

and eval_codes l fuel s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c fuel s in
    if None? s_opt then None else eval_codes tl fuel (Some?.v s_opt)

and eval_while b c fuel s0 =
  if fuel = 0 then None else
  let s0 = run (check (valid_ocmp b)) s0 in
  if not (eval_ocmp s0 b) then Some s0
  else
    match eval_code c (fuel - 1) s0 with
    | None -> None
    | Some s1 ->
      if s1.state.S.ok then eval_while b c (fuel - 1) s1  // success: continue to next iteration
      else Some s1  // failure: propagate failure immediately
