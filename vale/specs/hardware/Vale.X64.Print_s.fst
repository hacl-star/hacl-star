module Vale.X64.Print_s
open FStar.Mul

// Trusted code for producing assembly code

open Vale.X64.Machine_s
open Vale.X64.Instruction_s
open Vale.X64.Bytes_Code_s
open Vale.X64.Machine_Semantics_s
open FStar.IO

noeq type printer = {
  print_reg_name: reg_64 -> string;
  reg_prefix : unit -> string;
  mem_prefix : string -> string;
  maddr      : string -> option (string & string) -> string -> string;
  const      : int -> string;
  ins_name   : string -> list operand64 -> string;
  op_order   : string -> string -> string & string;
  align      : unit -> string;
  header     : unit -> string;
  footer     : unit -> string;
  proc_name  : string -> string;
  ret        : string -> string;
  sha256rnds2_explicit_xmm0: unit -> bool;
}

let print_reg_name (r:reg_64) : string =
  match r with
  | 0  -> "rax"
  | 1  -> "rbx"
  | 2  -> "rcx"
  | 3  -> "rdx"
  | 4  -> "rsi"
  | 5  -> "rdi"
  | 6  -> "rbp"
  | 7  -> "rsp"
  | 8  -> "r8"
  | 9  -> "r9"
  | 10 -> "r10"
  | 11 -> "r11"
  | 12 -> "r12"
  | 13 -> "r13"
  | 14 -> "r14"
  | 15 -> "r15"

let print_reg64 (r:reg_64) (p:printer) : string =
  p.reg_prefix() ^ p.print_reg_name r

let print_reg32 (r:reg_64) (p:printer) : string =
  p.reg_prefix() ^
  (match r with
  | 0 -> "eax"
  | 1 -> "ebx"
  | 2 -> "ecx"
  | 3 -> "edx"
  | 4 -> "esi"
  | 5 -> "edi"
  | 6 -> "ebp"
  | 7 -> "esp"
  | _ -> print_reg_name r ^ "d"
  )

let print_small_reg (r:reg_64) (p:printer) : string =
  p.reg_prefix() ^
  (match r with
  | 0 -> "al"
  | 1 -> "bl"
  | 2 -> "cl"
  | 3 -> "dl"
  | _ -> " !!! INVALID small operand !!!  Expected al, bl, cl, or dl."
  )

let print_maddr (m:maddr) (ptr_type:string) (reg_printer:reg -> printer -> string) (p:printer) : string =
  p.mem_prefix ptr_type ^
  ( match m with
    | MConst n -> p.const n
    | MReg r offset -> p.maddr (reg_printer r p) None (string_of_int offset)
    | MIndex base scale index offset ->
        p.maddr (reg_printer base p)
        (Some (string_of_int scale, reg_printer index p))
        (string_of_int offset)
  )
open FStar.UInt64

let print_reg_int (r:reg) (p:printer) : string =
  match r with
  | Reg 0 r -> print_reg64 r p
  | _ -> "!!! INVALID integer register !!!"

let print_operand (o:operand64) (p:printer) : string =
  match o with
  | OConst n ->
      if 0 <= n && n < pow2_64 then p.const n
      else "!!! INVALID constant: " ^ string_of_int n ^ " !!!"
  | OReg r -> print_reg64 r p
  | OMem (m, _) | OStack (m, _) -> print_maddr m "qword" print_reg_int p

let print_operand32 (o:operand64) (p:printer) : string =
  match o with
  | OConst n ->
      if 0 <= n && n < pow2_32 then p.const n
      else "!!! INVALID constant: " ^ string_of_int n ^ " !!!"
  | OReg r -> print_reg32 r p
  | OMem (m, _) | OStack (m, _) -> print_maddr m "dword" print_reg_int p

let print_small_operand (o:operand64) (p:printer) : string =
  match o with
  | OConst n ->
      if n < 64 then p.const n
      else "!!! INVALID constant: " ^ string_of_int n ^ " !!!!"
  | OReg r -> print_small_reg r p
  | _ -> "!!! INVALID small operand !!! Expected al, bl, cl, or dl."

let print_imm8 (i:int) (p:printer) : string =
  p.const i

let print_xmm (x:reg_xmm) (p:printer) : string =
  p.reg_prefix () ^ "xmm" ^ string_of_int x

let print_mov128_op (o:operand128) (p:printer) : string =
  match o with
  | OConst _ -> "!!! INVALID xmm constants not allowed !!!"
  | OReg x -> print_xmm x p
  | OMem (m, _) | OStack (m, _) -> print_maddr m "xmmword" print_reg_int p

assume val print_any: 'a -> string

let print_shift_operand (o:operand64) (p:printer) : string =
  match o with
  | OConst n ->
      if n < 64 then p.const n
      else "!!! INVALID shift operand: " ^ string_of_int n ^ " is too large !!!"
  | OReg rRcx -> print_small_reg (OReg?.r o) p
  | _ -> "!!! INVALID shift operand !!! Expected constant or cl."

let cmp_not(o:ocmp) : ocmp =
  match o with
  | OEq o1 o2 -> ONe o1 o2
  | ONe o1 o2 -> OEq o1 o2
  | OLe o1 o2 -> OGt o1 o2
  | OGe o1 o2 -> OLt o1 o2
  | OLt o1 o2 -> OGe o1 o2
  | OGt o1 o2 -> OLe o1 o2

// Sanity check
let _ = assert (forall o . o == cmp_not (cmp_not o))

let print_pair (dst src:string) (p:printer) : string =
  let first, second = p.op_order dst src in
    first ^ ", " ^ second

let print_instr (ip:instr_print) (p:printer) : string =
  let Print name kind oprs = ip in
  let (suffix, oprs) =
    match kind with
    | POpcode -> (false, oprs)
    | PSuffix -> (true, oprs)
    | PrintPSha256rnds2 ->
        (false, (if p.sha256rnds2_explicit_xmm0 () then oprs @ [PXmm (OReg 0)] else oprs))
    in
  let rec get_operands (oprs:list instr_print_operand) : list operand64 =
    match oprs with
    | [] -> []
    | (P8 o)::oprs -> o::(get_operands oprs)
    | (P16 o)::oprs -> o::(get_operands oprs)
    | (P32 o)::oprs -> o::(get_operands oprs)
    | (P64 o)::oprs -> o::(get_operands oprs)
    | _::oprs -> get_operands oprs
    in
  let (opcode, space) =
    match suffix with
    | false -> (name, " ")
    | true -> (p.ins_name name (get_operands oprs), "")
    in
  let print_operand (po:instr_print_operand) : string =
    match po with
    | P8 o -> print_small_operand o p
    | P16 o -> "!!! UNSUPPORTED OPERAND !!!"
    | P32 o -> print_operand32 o p
    | P64 o -> print_operand o p
    | PXmm o -> print_mov128_op o p
    | PImm i -> p.const i
    | PShift o -> print_shift_operand o p
    in
  let rec print_operands (oprs:list instr_print_operand) : string =
    match oprs with
    | [] -> ""
    | [o] -> print_operand o
    | o::oprs -> print_pair (print_operand o) (print_operands oprs) p
    in
  match oprs with
  | [] -> "  " ^ opcode
  | _ -> "  " ^ opcode ^ space ^ (print_operands oprs)

let print_ins (ins:ins) (p:printer) : string =
  let print_pair (dst src:string) = print_pair dst src p in
  let print_op_pair (dst:operand64) (src:operand64) (print_dst:operand64 -> printer -> string) (print_src:operand64 -> printer -> string) =
    print_pair (print_dst dst p) (print_src src p)
  in
  let print_ops (dst:operand64) (src:operand64) =
    print_op_pair dst src print_operand print_operand
  in
  let print_shift (dst:operand64) (amount:operand64) =
    print_op_pair dst amount print_operand print_shift_operand
  in
  let print_xmm_op (dst:reg_xmm) (src:operand64) =
    let first, second = p.op_order (print_xmm dst p) (print_operand src p) in
      first ^ ", " ^ second
  in
  let print_xmm_op32 (dst:reg_xmm) (src:operand64) =
    let first, second = p.op_order (print_xmm dst p) (print_operand32 src p) in
      first ^ ", " ^ second
  in
  let print_op_xmm (dst:operand64) (src:reg_xmm) =
    let first, second = p.op_order (print_operand dst p) (print_xmm src p) in
      first ^ ", " ^ second
  in
  let print_xmms (dst:reg_xmm) (src:reg_xmm) =
    let first, second = p.op_order (print_xmm dst p) (print_xmm src p) in
      first ^ ", " ^ second
  in
  let print_xmms_3 (dst src1 src2:reg_xmm) =
    print_pair (print_xmm dst p) (print_xmms src1 src2)
  in
  let print_vpxor (dst src1:reg_xmm) (src2:operand128) =
    print_pair (print_xmm dst p) (print_pair (print_xmm src1 p) (print_mov128_op src2 p))
  in
  let print_instr (ip:instr_print) : string = print_instr ip p in
  match ins with
  | Instr (InstrTypeRecord i) oprs _ -> print_instr (instr_printer i oprs)
  | Push src _     -> p.ins_name "  push" [src] ^ print_operand src p
  | Pop dst _      -> p.ins_name "  pop"  [dst] ^ print_operand dst p
  | Alloc n       -> p.ins_name "  sub" [OReg rRsp; OConst n] ^ print_ops (OReg rRsp) (OConst n)
  | Dealloc n       -> p.ins_name "  add" [OReg rRsp; OConst n] ^ print_ops (OReg rRsp) (OConst n)

let print_cmp (c:ocmp) (counter:int) (p:printer) : string =
  let print_ops (o1:operand64) (o2:operand64) : string =
    let first, second = p.op_order (print_operand o1 p) (print_operand o2 p) in
    "  cmp " ^ first ^ ", " ^ second ^ "\n"
  in
  match c with
  | OEq o1 o2 -> print_ops o1 o2 ^ "  je " ^ "L" ^ string_of_int counter ^ "\n"
  | ONe o1 o2 -> print_ops o1 o2 ^ "  jne "^ "L" ^ string_of_int counter ^ "\n"
  | OLe o1 o2 -> print_ops o1 o2 ^ "  jbe "^ "L" ^ string_of_int counter ^ "\n"
  | OGe o1 o2 -> print_ops o1 o2 ^ "  jae "^ "L" ^ string_of_int counter ^ "\n"
  | OLt o1 o2 -> print_ops o1 o2 ^ "  jb " ^ "L" ^ string_of_int counter ^ "\n"
  | OGt o1 o2 -> print_ops o1 o2 ^ "  ja " ^ "L" ^ string_of_int counter ^ "\n"

let rec print_block (b:codes) (n:int) (p:printer) : string & int =
  match b with
  | Nil -> ("", n)
  | Ins (Instr _ _ (AnnotateSpace _)) :: tail -> print_block tail n p
  | Ins (Instr _ _ (AnnotateGhost _)) :: tail -> print_block tail n p
  | head :: tail ->
    let (head_str, n') = print_code head n p in
    let (rest, n'') = print_block tail n' p in
    (head_str ^ rest, n'')
and print_code (c:code) (n:int) (p:printer) : string & int =
  match c with
  | Ins ins -> (print_ins ins p ^ "\n", n)
  | Block b -> print_block b n p
  | IfElse cond true_code false_code ->
    let n1 = n in
    let n2 = n + 1 in
    let cmp = print_cmp (cmp_not cond) n1 p in
    let (true_str, n') = print_code true_code (n + 2) p in
    let jmp = "  jmp L" ^ string_of_int n2 ^ "\n" in
    let label1 = "L" ^ string_of_int n1 ^ ":\n" in
    let (false_str, n') = print_code false_code n' p in
    let label2 = "L" ^ string_of_int n2 ^ ":\n" in
    (cmp ^ true_str ^ jmp ^ label1 ^ false_str ^ label2, n')
  | While cond body ->
    let n1 = n in
    let n2 = n + 1 in
    let jmp = "  jmp L" ^ string_of_int n2 ^ "\n" in
    let label1 = p.align() ^ " 16\nL" ^ string_of_int n1 ^ ":\n" in
    let (body_str, n') = print_code body (n + 2) p in
    let label2 = p.align() ^ " 16\nL" ^ string_of_int n2 ^ ":\n" in
    let cmp = print_cmp cond n1 p in
    (jmp ^ label1 ^ body_str ^ label2 ^ cmp, n')

let print_header (p:printer) =
  print_string (p.header())

let print_proc (name:string) (code:code) (label:int) (p:printer) : FStar.All.ML int =
  let proc = p.proc_name name in
  let code_str, final_label = print_code code label p in
  let ret = p.ret name in
  print_string (proc ^ code_str ^ ret);
  final_label

let print_footer (p:printer) =
  print_string (p.footer())


(* Concrete printers for MASM and GCC syntax *)
let masm : printer =
  let reg_prefix unit = "" in
  let mem_prefix (ptr_type:string) = ptr_type ^ " ptr " in
  let maddr (base:string) (adj:option(string & string)) (offset:string) =
    match adj with
    | None -> "[" ^ base ^ " + " ^ offset ^ "]"
    | Some (scale, index) -> "[" ^ base ^ " + " ^ scale ^ " * " ^ index ^ " + " ^ offset ^ "]"
  in
  let const (n:int) = string_of_int n in
  let ins_name (name:string) (ops:list operand64) : string = name ^ " " in
  let op_order dst src = dst, src in
  let align() = "ALIGN" in
  let header() = ".code\n" in
  let footer() = "end\n" in
  let proc_name (name:string) = "ALIGN 16\n" ^ name ^ " proc\n" in
  let ret (name:string) = "  ret\n" ^ name ^ " endp\n" in
  {
  print_reg_name = print_reg_name;
  reg_prefix = reg_prefix;
  mem_prefix = mem_prefix;
  maddr      = maddr;
  const      = const;
  ins_name   = ins_name;
  op_order   = op_order;
  align      = align;
  header     = header;
  footer     = footer;
  proc_name  = proc_name;
  ret        = ret;
  sha256rnds2_explicit_xmm0 = (fun unit -> true);
  }

let gcc : printer =
  let reg_prefix unit = "%" in
  let mem_prefix (ptr_type:string) = "" in
  let maddr (base:string) (adj:option(string & string)) (offset:string) =
    match adj with
    | None -> offset ^ "(" ^ base ^ ")"
    | Some (scale, index) -> offset ^ " (" ^ base ^ ", " ^ scale ^ ", " ^ index ^ ")"
  in
  let const (n:int) = "$" ^ string_of_int n in
  let rec ins_name (name:string) (ops:list operand64) : string =
    match ops with
    | Nil -> name ^ " "
    | OMem _ :: _ -> name ^ "q "
    | _ :: tail -> ins_name name tail
  in
  let op_order dst src = src, dst in
  let align() = ".balign" in
  let header() = ".text\n" in
  let footer() = "\n" in
  let proc_name (name:string) = ".global " ^ name ^ "\n" ^ name ^ ":\n" in
  let ret (name:string) = "  ret\n\n" in
  {
  print_reg_name = print_reg_name;
  reg_prefix = reg_prefix;
  mem_prefix = mem_prefix;
  maddr      = maddr;
  const      = const;
  ins_name   = ins_name;
  op_order   = op_order;
  align      = align;
  header     = header;
  footer     = footer;
  proc_name  = proc_name;
  ret        = ret;
  sha256rnds2_explicit_xmm0 = (fun unit -> false);
  }
