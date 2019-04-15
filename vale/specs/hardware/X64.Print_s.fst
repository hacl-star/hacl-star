module X64.Print_s

// Trusted code for producing assembly code

open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Taint_Semantics_s
open FStar.IO

noeq type printer = {
  reg_prefix : unit -> string;
  mem_prefix : string -> string;
  maddr      : string -> option(string * string) -> string -> string;
  const      : int -> string;
  ins_name   : string -> list operand -> string;
  op_order   : string -> string -> string * string;
  align      : unit -> string;
  header     : unit -> string;
  footer     : unit -> string;
  proc_name  : string -> string;
  ret        : string -> string;
  sha256rnds2_explicit_xmm0: unit -> bool;
}

let print_reg_name (r:reg) =
  match r with
  | Rax -> "rax"
  | Rbx -> "rbx"
  | Rcx -> "rcx"
  | Rdx -> "rdx"
  | Rsi -> "rsi"
  | Rdi -> "rdi"
  | Rbp -> "rbp"
  | Rsp -> "rsp"
  | R8  -> "r8"
  | R9  -> "r9"
  | R10 -> "r10"
  | R11 -> "r11"
  | R12 -> "r12"
  | R13 -> "r13"
  | R14 -> "r14"
  | R15 -> "r15"

let print_reg (r:reg) (p:printer) =
  p.reg_prefix() ^ print_reg_name r

let print_reg32 (r:reg) (p:printer) =
  p.reg_prefix() ^
  (match r with
  | Rax -> "eax"
  | Rbx -> "ebx"
  | Rcx -> "ecx"
  | Rdx -> "edx"
  | Rsi -> "esi"
  | Rdi -> "edi"
  | Rbp -> "ebp"
  | Rsp -> "esp"
  | _ -> print_reg_name r ^ "d"
  )

let print_small_reg (r:reg) (p:printer) =
  p.reg_prefix() ^
  (match r with
  | Rax -> "al"
  | Rbx -> "bl"
  | Rcx -> "cl"
  | Rdx -> "dl"
  | _ -> " !!! INVALID small operand !!!  Expected al, bl, cl, or dl."
  )

let print_maddr (m:maddr) (ptr_type:string) (reg_printer:reg->printer->string) (p:printer) =
  p.mem_prefix ptr_type ^
  (match m with
     | MConst n -> p.const n
     | MReg r offset -> p.maddr (reg_printer r p) None (string_of_int offset)
     | MIndex base scale index offset ->
          p.maddr (reg_printer base p)
          (Some (string_of_int scale, reg_printer index p))
          (string_of_int offset)
   )
open FStar.UInt64

let print_operand (o:operand) (p:printer) =
  match o with
  | OConst n ->
      if 0 <= n && n < pow2_64 then p.const n
      else "!!! INVALID constant: " ^ string_of_int n ^ " !!!"
  | OReg r -> print_reg r p
  | OMem m | OStack m -> print_maddr m "qword" print_reg p

let print_operand32 (o:operand) (p:printer) =
  match o with
  | OConst n ->
      if 0 <= n && n < pow2_32 then p.const n
      else "!!! INVALID constant: " ^ string_of_int n ^ " !!!"
  | OReg r -> print_reg32 r p
  | OMem m | OStack m -> print_maddr m "dword" print_reg32 p

let print_small_operand (o:operand) (p:printer) =
  match o with
  | OConst n ->
      if n < 64 then p.const n
      else "!!! INVALID constant: " ^ string_of_int n ^ " !!!!"
  | OReg r -> print_small_reg r p
  | _ -> "!!! INVALID small operand !!! Expected al, bl, cl, or dl."

let print_imm8 (i:int) (p:printer) =
  p.const i

let print_xmm (x:xmm) (p:printer) =
  p.reg_prefix() ^ "xmm" ^ string_of_int x

let print_mov128_op (o:mov128_op) (p:printer) =
  match o with
  | Mov128Xmm x -> print_xmm x p
  | Mov128Mem m | Mov128Stack m -> print_maddr m "xmmword" print_reg p

assume val print_any: 'a -> string

let print_shift_operand (o:operand) (p:printer) =
  match o with
  | OConst n ->
      if n < 64 then p.const n
      else "!!! INVALID shift operand: " ^ string_of_int n ^ " is too large !!!"
  | OReg Rcx -> print_small_reg (OReg?.r o) p
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

let print_ins (ins:tainted_ins) (p:printer) =
  let print_pair (dst src:string) =
    let first, second = p.op_order dst src in
      first ^ ", " ^ second
  in
  let print_op_pair (dst:operand) (src:operand) (print_dst:operand->printer->string) (print_src:operand->printer-> string) =
    print_pair (print_dst dst p) (print_src src p)
  in
  let print_ops (dst:operand) (src:operand) =
    print_op_pair dst src print_operand print_operand
  in
  let print_shift (dst:operand) (amount:operand) =
    print_op_pair dst amount print_operand print_shift_operand
  in
  let print_xmm_op (dst:xmm) (src:operand) =
    let first, second = p.op_order (print_xmm dst p) (print_operand src p) in
      first ^ ", " ^ second
  in
  let print_xmm_op32 (dst:xmm) (src:operand) =
    let first, second = p.op_order (print_xmm dst p) (print_operand32 src p) in
      first ^ ", " ^ second
  in
  let print_op_xmm (dst:operand) (src:xmm) =
    let first, second = p.op_order (print_operand dst p) (print_xmm src p) in
      first ^ ", " ^ second
  in
  let print_xmms (dst:xmm) (src:xmm) =
    let first, second = p.op_order (print_xmm dst p) (print_xmm src p) in
      first ^ ", " ^ second
  in
  let print_xmms_3 (dst src1 src2:xmm) =
    print_pair (print_xmm dst p) (print_xmms src1 src2)
  in
  let print_vpxor (dst src1:xmm) (src2:mov128_op) =
    print_pair (print_xmm dst p) (print_pair (print_xmm src1 p) (print_mov128_op src2 p))
  in
  let ins = ins.i in
  match ins with
  | Cpuid -> "  cpuid"
  | Mov64 dst src -> p.ins_name   "  mov"   [dst; src] ^ print_ops dst src
  | MovBe64 dst src -> p.ins_name "  movbe" [dst; src] ^ print_ops dst src
  | Cmovc64 dst src -> p.ins_name "  cmovc" [dst; src] ^ print_ops dst src  
  | Add64 dst src -> p.ins_name   "  add"   [dst; src] ^ print_ops dst src
  | AddLea64 dst src1 src2 -> let name = p.ins_name "  lea" [dst; src1; src2] in
                             let src = OMem (if OReg? src1 && OConst? src2 then
                                                MReg (OReg?.r src1) (OConst?.n src2)
                                             else if OReg? src1 && OReg? src2 then
                                               MIndex (OReg?.r src1) 1 (OReg?.r src2) 0
                                             else
                                               MConst pow2_128) in  // Shouldn't hit this, but if we do, assembler will complain
                             name ^ print_ops dst src
  | AddCarry64 dst src -> p.ins_name "  adc" [dst; src] ^ print_ops dst src
  | Adcx64 dst src -> p.ins_name "  adcx" [dst; src] ^ print_ops dst src
  | Adox64 dst src -> p.ins_name "  adox" [dst; src] ^ print_ops dst src
  | Sub64 dst src -> p.ins_name "  sub" [dst; src] ^ print_ops dst src
  | Sbb64 dst src -> p.ins_name "  sbb" [dst; src] ^ print_ops dst src
  | Mul64 src -> p.ins_name "  mul" [src] ^ (print_operand src p)
  | Mulx64 dst_hi dst_lo src ->
    let dst_s = print_ops dst_hi dst_lo in
    p.ins_name "  mulx" [dst_hi; dst_lo; src] ^ print_pair dst_s (print_operand src p)
  | IMul64 dst src -> p.ins_name "  imul" [dst; src] ^ print_ops dst src
  | Xor64 dst src -> p.ins_name "  xor" [dst; src] ^ print_ops dst src
  | And64 dst src -> p.ins_name "  and" [dst; src] ^ print_ops dst src
  | Shr64 dst amt -> p.ins_name "  shr" [dst; amt] ^ print_shift dst amt
  | Shl64 dst amt -> p.ins_name "  shl" [dst; amt] ^ print_shift dst amt
  | Push src      -> p.ins_name "  push" [src] ^ print_operand src p
  | Pop dst       -> p.ins_name "  pop"  [dst] ^ print_operand dst p
  | Alloc n       -> p.ins_name "  sub" [OReg Rsp; OConst n] ^ print_ops (OReg Rsp) (OConst n)
  | Dealloc n       -> p.ins_name "  add" [OReg Rsp; OConst n] ^ print_ops (OReg Rsp) (OConst n)
  | Paddd dst src                -> "  paddd "      ^ print_xmms dst src
  |VPaddd dst src1 src2          -> "  vpaddd "     ^ print_xmms_3 dst src1 src2
  | Pxor dst src                 -> "  pxor "       ^ print_xmms dst src
  |VPxor dst src1 src2           -> "  vpxor "      ^ print_vpxor dst src1 src2
  | Pand dst src                 -> "  pand "       ^ print_xmms dst src
  | Pslld dst amt                -> "  pslld "      ^ print_pair (print_xmm dst p) (print_imm8 amt p)
  | Psrld dst amt                -> "  psrld "      ^ print_pair (print_xmm dst p) (print_imm8 amt p)
  | Psrldq dst amt               -> "  psrldq "     ^ print_pair (print_xmm dst p) (print_imm8 amt p)
  | Palignr dst src amount       -> "  palignr "    ^ print_pair (print_xmms dst src) (print_imm8 amount p)
  |VPalignr dst src1 src2 amount -> "  vpalignr "   ^ print_pair (print_xmms_3 dst src1 src2) (print_imm8 amount p)  
  | Shufpd dst src perm          -> "  shufpd "     ^ print_pair (print_xmms dst src) (print_imm8 perm p)
  |VShufpd dst src1 src2 perm    -> "  vshufpd "    ^ print_pair (print_xmms_3 dst src1 src2) (print_imm8 perm p)
  | Pshufb dst src               -> "  pshufb "     ^ print_xmms dst src
  |VPshufb dst src1 src2         -> "  vpshufb "    ^ print_xmms_3 dst src1 src2 
  | Pshufd dst src count         -> "  pshufd "     ^ print_pair (print_xmms dst src) (print_imm8 count p)
  | Pcmpeqd dst src              -> "  pcmpeqd "    ^ print_xmms dst src
  | Pextrq dst src index         -> "  pextrq "     ^ print_pair (print_op_xmm dst src) (print_imm8 index p)
  | Pinsrd dst src index         -> "  pinsrd "     ^ print_pair (print_xmm_op32 dst src) (print_imm8 index p)
  | Pinsrq dst src index         -> "  pinsrq "     ^ print_pair (print_xmm_op dst src) (print_imm8 index p)
  | VPSLLDQ dst src count        -> "  vpslldq "    ^ print_pair (print_xmms dst src) (print_imm8 count p)
  | Vpsrldq dst src count        -> "  vpsrldq "    ^ print_pair (print_xmms dst src) (print_imm8 count p)
  | MOVDQU dst src               -> "  movdqu "     ^ print_pair (print_mov128_op dst p) (print_mov128_op src p)
  | Pclmulqdq dst src imm        -> "  pclmulqdq "  ^ print_pair (print_xmms dst src) (print_imm8 imm p)
  |VPclmulqdq dst src1 src2 imm  -> "  vpclmulqdq " ^ print_pair (print_xmms_3 dst src1 src2) (print_imm8 imm p)  
  | AESNI_enc dst src            -> "  aesenc "     ^ print_xmms dst src
  | AESNI_enc_last dst src       -> "  aesenclast " ^ print_xmms dst src
  |VAESNI_enc dst src1 src2      -> "  vaesenc "     ^ print_xmms_3 dst src1 src2 
  |VAESNI_enc_last dst src1 src2 -> "  vaesenclast " ^ print_xmms_3 dst src1 src2
  | AESNI_dec dst src      -> "  aesdec "     ^ print_xmms dst src
  | AESNI_dec_last dst src -> "  aesdeclast " ^ print_xmms dst src
  | AESNI_imc dst src      -> "  aesimc "     ^ print_xmms dst src
  | AESNI_keygen_assist dst src imm -> "  aeskeygenassist " ^ print_pair (print_xmms dst src) (print_imm8 imm p)
  | SHA256_rnds2 dst src   -> if p.sha256rnds2_explicit_xmm0() then 
                               "  sha256rnds2 " ^ print_pair (print_xmms dst src) (print_xmm 0 p)
                             else 
                               "  sha256rnds2 " ^ print_xmms dst src
  | SHA256_msg1 dst src    -> "  sha256msg1 "  ^ print_xmms dst src
  | SHA256_msg2 dst src    -> "  sha256msg2 "  ^ print_xmms dst src
    

let print_cmp (c:ocmp) (counter:int) (p:printer) : string =
  let print_ops (o1:operand) (o2:operand) : string =
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

let rec print_block (b:tainted_codes) (n:int) (p:printer) : string * int =
  match b with
  | Nil -> "", n
  | head :: tail ->
    let head_str, n' = print_code head n p in
    let rest, n'' = print_block tail n' p in
    head_str ^ rest, n''
and print_code (c:tainted_code) (n:int) (p:printer) : string * int =
  match c with
  | Ins ins -> (print_ins ins p ^ "\n", n)
  | Block b -> print_block b n p
  | IfElse cond true_code false_code ->
    let n1 = n in
    let n2 = n + 1 in
    let cmp = print_cmp (cmp_not cond.o) n1 p in
    let true_str, n' = print_code true_code (n + 2) p in
    let jmp = "  jmp L" ^ string_of_int n2 ^ "\n" in
    let label1 = "L" ^ string_of_int n1 ^ ":\n" in
    let false_str, n' = print_code false_code n' p in
    let label2 = "L" ^ string_of_int n2 ^ ":\n" in
    cmp ^ true_str ^ jmp ^ label1 ^ false_str ^ label2, n'
  | While cond body ->
    let n1 = n in
    let n2 = n + 1 in
    let jmp = "  jmp L" ^ string_of_int n2 ^ "\n" in
    let label1 = p.align() ^ " 16\nL" ^ string_of_int n1 ^ ":\n" in
    let body_str, n' = print_code body (n + 2) p in
    let label2 = p.align() ^ " 16\nL" ^ string_of_int n2 ^ ":\n" in
    let cmp = print_cmp cond.o n1 p in
    jmp ^ label1 ^ body_str ^ label2 ^ cmp, n'

let print_header (p:printer) =
  print_string (p.header())

let print_proc (name:string) (code:tainted_code) (label:int) (p:printer) : FStar.All.ML int =
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
  let maddr (base:string) (adj:option(string * string)) (offset:string) =
    match adj with
    | None -> "[" ^ base ^ " + " ^ offset ^ "]"
    | Some (scale, index) -> "[" ^ base ^ " + " ^ scale ^ " * " ^ index ^ " + " ^ offset ^ "]"
  in
  let const (n:int) = string_of_int n in
  let ins_name (name:string) (ops:list operand) : string = name ^ " " in
  let op_order dst src = dst, src in
  let align() = "ALIGN" in
  let header() = ".code\n" in
  let footer() = "end\n" in
  let proc_name (name:string) = "ALIGN 16\n" ^ name ^ " proc\n" in
  let ret (name:string) = "  ret\n" ^ name ^ " endp\n" in
  {
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
  let maddr (base:string) (adj:option(string * string)) (offset:string) =
    match adj with
    | None -> offset ^ "(" ^ base ^ ")"
    | Some (scale, index) -> offset ^ " (" ^ base ^ ", " ^ scale ^ ", " ^ index ^ ")"
  in
  let const (n:int) = "$" ^ string_of_int n in
  let rec ins_name (name:string) (ops:list operand) : string =
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
