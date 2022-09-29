module Vale.PPC64LE.Print_s

// Trusted code for producing assembly code

open Vale.PPC64LE.Machine_s
open Vale.PPC64LE.Semantics_s
open FStar.IO

noeq type printer = {
  reg_prefix : unit -> string;
  vec_prefix : unit -> string;
  vsr_prefix : unit -> string;
  maddr      : string -> string -> string;
  const      : int -> string;
  align      : unit -> string;
  header     : unit -> string;
  footer     : unit -> string;
  proc_name  : string -> string;
  ret        : string -> string;
}

let print_reg (r:reg) (p:printer) =
  p.reg_prefix() ^ string_of_int r

let print_vec (v:vec) (vsr:bool) (p:printer) =
  if vsr then p.vsr_prefix() ^ "32+" ^ string_of_int v
  else p.vec_prefix() ^ string_of_int v

let print_maddr (m:maddr) (p:printer) =
  p.maddr (string_of_int m.offset) (print_reg m.address p)

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

let print_first_cmp_opr (o:cmp_opr) (p:printer) =
  match o with
  | CReg r -> print_reg r p
  | _ -> "!!! INVALID first compare operand !!! Expected general purpose register."

let print_ins (ins:ins) (p:printer) =
  let print_pair (o1 o2:string) =
    o1 ^ ", " ^ o2
  in
  let print_triple (o1 o2 o3:string) =
    o1 ^ ", " ^ o2 ^ ", " ^ o3
  in
  let print_quadruple (o1 o2 o3 o4:string) =
    o1 ^ ", " ^ o2 ^ ", " ^ o3 ^ ", " ^ o4
  in
  let print_reg_pair (dst src:reg) =
    print_pair (print_reg dst p) (print_reg src p)
  in
  let print_reg_mem (o1:reg) (o2:maddr) =
    print_pair (print_reg o1 p) (print_maddr o2 p)
  in
  let print_reg_triple (dst src1 src2:reg) =
    print_triple (print_reg dst p) (print_reg src1 p) (print_reg src2 p)
  in
  let print_reg_imm (dst:reg) (src:int) =
    print_pair (print_reg dst p) (p.const src)
  in
  let print_reg_pair_imm (dst src1:reg) (src2:int) =
    print_triple (print_reg dst p) (print_reg src1 p) (p.const src2)
  in
  let print_reg_vec (dst:reg) (src:vec) (vsr:bool) =
    print_pair (print_reg dst p) (print_vec src vsr p)
  in
  let print_vec_reg_pair (dst:vec) (src1 src2:reg) (vsr:bool) =
    print_triple (print_vec dst vsr p) (print_reg src1 p) (print_reg src2 p)
  in
  let print_vec_triple (dst src1 src2:vec) (vsr:bool) =
    print_triple (print_vec dst vsr p) (print_vec src1 vsr p) (print_vec src2 vsr p)
  in
  let print_vec_quadruple (dst src1 src2 src3:vec) (vsr:bool) =
    print_quadruple (print_vec dst vsr p) (print_vec src1 vsr p) (print_vec src2 vsr p) (print_vec src3 vsr p)
  in
  let print_vec_triple_imm (dst src1 src2:vec) (count:int) (vsr:bool) =
    print_quadruple (print_vec dst vsr p) (print_vec src1 vsr p) (print_vec src2 vsr p) (p.const count)
  in
  let print_vec_mem (o1:vec) (o2:maddr) (vsr:bool) =
    print_pair (print_vec o1 vsr p) (print_maddr o2 p)
  in
  let print_vec_pair_imm_pair (dst src:vec) (s0 s1:int) (vsr:bool) =
    print_quadruple (print_vec dst vsr p) (print_vec src vsr p) (p.const s0) (p.const s1)
  in
  match ins with
  | Move dst src -> "  mr " ^ print_reg_pair dst src
  | Load64 dst base offset -> "  ld " ^ print_reg_mem dst ({ address = base; offset = offset })
  | Store64 src base offset -> "  std " ^ print_reg_mem src ({ address = base; offset = offset })
  | LoadImm64 dst src -> "  li " ^ print_reg_imm dst src
  | AddLa dst src1 src2 -> "  la " ^ print_reg_mem dst ({ address = src1; offset = src2 })
  | Add dst src1 src2 -> "  add " ^ print_reg_triple dst src1 src2
  | AddImm dst src1 src2 -> "  addi " ^ print_reg_pair_imm dst src1 src2
  | AddExtended dst src1 src2 -> "  adde " ^ print_reg_triple dst src1 src2
  | AddExtendedOV dst src1 src2 -> "  addex " ^ print_reg_triple dst src1 src2
  | Sub dst src1 src2 -> "  sub " ^ print_reg_triple dst src1 src2
  | SubImm dst src1 src2 -> "  subi " ^ print_reg_pair_imm dst src1 src2
  | MulLow64 dst src1 src2 -> "  mulld " ^ print_reg_triple dst src1 src2
  | MulHigh64U dst src1 src2 -> "  mulhdu " ^ print_reg_triple dst src1 src2
  | Xor dst src1 src2 -> "  xor " ^ print_reg_triple dst src1 src2
  | And dst src1 src2 -> "  and " ^ print_reg_triple dst src1 src2
  | Sr64Imm dst src1 src2 -> "  srdi " ^ print_reg_pair_imm dst src1 src2
  | Sl64Imm dst src1 src2 -> "  sldi " ^ print_reg_pair_imm dst src1 src2
  | Mfvsrd dst src -> "  mfvsrd " ^ print_reg_vec dst src true
  | Mfvsrld dst src -> "  mfvsrld " ^ print_reg_vec dst src true
  | Mtvsrdd dst src1 src2 -> "  mtvsrdd " ^ print_vec_reg_pair dst src1 src2 true
  | Vadduwm dst src1 src2 -> "  vadduwm " ^ print_vec_triple dst src1 src2 false
  | Vxor dst src1 src2 -> "  vxor " ^ print_vec_triple dst src1 src2 false
  | Vslw dst src1 src2 -> "  vslw " ^ print_vec_triple dst src1 src2 false
  | Vsrw dst src1 src2 -> "  vsrw " ^ print_vec_triple dst src1 src2 false
  | Vcmpequw dst src1 src2 -> "  vcmpequw " ^ print_vec_triple dst src1 src2 false
  | Vsldoi dst src1 src2 count -> "  vsldoi " ^ print_vec_triple_imm dst src1 src2 count false
  | Vmrghw dst src1 src2 -> "  vmrghw " ^ print_vec_triple dst src1 src2 false
  | Xxmrghd dst src1 src2 -> "  xxmrghd " ^ print_vec_triple dst src1 src2 true
  | Vsel dst src1 src2 sel -> "  vsel " ^ print_vec_quadruple dst src1 src2 sel false
  | Load128 dst base offset -> "  lvx " ^ print_vec_reg_pair dst offset base false
  | Store128 src base offset -> "  stvx " ^ print_vec_reg_pair src offset base false
  | Load128Word4 dst base -> "  lxvw4x " ^ print_vec_reg_pair dst 0 base true
  | Load128Word4Index dst base offset -> "  lxvw4x " ^ print_vec_reg_pair dst offset base true
  | Store128Word4 src base -> "  stxvw4x " ^ print_vec_reg_pair src 0 base true
  | Store128Word4Index src base offset -> "  stxvw4x " ^ print_vec_reg_pair src offset base true
  | Load128Byte16 dst base -> "  lxvb16x " ^ print_vec_reg_pair dst 0 base true
  | Load128Byte16Index dst base offset -> "  lxvb16x " ^ print_vec_reg_pair dst offset base true
  | Store128Byte16 src base -> "  stxvb16x " ^ print_vec_reg_pair src 0 base true
  | Store128Byte16Index src base offset -> "  stxvb16x " ^ print_vec_reg_pair src offset base true
  | Vshasigmaw0 dst src -> "  vshasigmaw " ^ print_vec_pair_imm_pair dst src 0 0 false
  | Vshasigmaw1 dst src -> "  vshasigmaw " ^ print_vec_pair_imm_pair dst src 0 15 false
  | Vshasigmaw2 dst src -> "  vshasigmaw " ^ print_vec_pair_imm_pair dst src 1 0 false
  | Vshasigmaw3 dst src -> "  vshasigmaw " ^ print_vec_pair_imm_pair dst src 1 15 false
  | Alloc n -> "  subi " ^ print_reg_pair_imm 1 1 n
  | Dealloc n -> "  addi " ^ print_reg_pair_imm 1 1 n
  | StoreStack128 src t offset -> "  stxv " ^ print_vec_mem src ({ address = 1; offset = offset }) true
  | LoadStack128 dst t offset -> "  lxv " ^ print_vec_mem dst ({ address = 1; offset = offset }) true
  | Ghost _ -> ""
let print_cmp (c:ocmp) (counter:int) (p:printer) : string =
  let print_cmp_ops (o1:cmp_opr) (o2:cmp_opr) : string =
    match o2 with
    | CReg r -> "  cmpld " ^ (print_first_cmp_opr o1 p) ^ ", " ^ (print_reg r p) ^ "\n"
    | CImm n -> "  cmpldi " ^ (print_first_cmp_opr o1 p) ^ ", " ^ (string_of_int n) ^ "\n"
  in
  match c with
  | OEq o1 o2 -> print_cmp_ops o1 o2 ^ "  beq " ^ "L" ^ string_of_int counter ^ "\n"
  | ONe o1 o2 -> print_cmp_ops o1 o2 ^ "  bne "^ "L" ^ string_of_int counter ^ "\n"
  | OLe o1 o2 -> print_cmp_ops o1 o2 ^ "  ble "^ "L" ^ string_of_int counter ^ "\n"
  | OGe o1 o2 -> print_cmp_ops o1 o2 ^ "  bge "^ "L" ^ string_of_int counter ^ "\n"
  | OLt o1 o2 -> print_cmp_ops o1 o2 ^ "  blt " ^ "L" ^ string_of_int counter ^ "\n"
  | OGt o1 o2 -> print_cmp_ops o1 o2 ^ "  bgt " ^ "L" ^ string_of_int counter ^ "\n"

let rec print_block (b:codes) (n:int) (p:printer) : string & int =
  match b with
  | Nil -> ("", n)
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
    let branch = "  b L" ^ string_of_int n2 ^ "\n" in
    let label1 = "L" ^ string_of_int n1 ^ ":\n" in
    let (false_str, n') = print_code false_code n' p in
    let label2 = "L" ^ string_of_int n2 ^ ":\n" in
    (cmp ^ true_str ^ branch ^ label1 ^ false_str ^ label2, n')
  | While cond body ->
    let n1 = n in
    let n2 = n + 1 in
    let branch = "  b L" ^ string_of_int n2 ^ "\n" in
    let label1 = p.align() ^ " 4\nL" ^ string_of_int n1 ^ ":\n" in
    let (body_str, n') = print_code body (n + 2) p in
    let label2 = p.align() ^ " 4\nL" ^ string_of_int n2 ^ ":\n" in
    let cmp = print_cmp cond n1 p in
    (branch ^ label1 ^ body_str ^ label2 ^ cmp, n')

let print_header (p:printer) =
  print_string (p.header())

let print_proc (name:string) (code:code) (label:int) (p:printer) : FStar.All.ML int =
  let proc = p.proc_name name in
  let (code_str, final_label) = print_code code label p in
  let ret = p.ret name in
  print_string (proc ^ code_str ^ ret);
  final_label

let print_footer (p:printer) =
  print_string (p.footer())

// Concrete printers for GCC syntax
let gcc : printer =
  let reg_prefix unit = "" in
  let vec_prefix unit = "" in
  let vsr_prefix unit = "" in
  let maddr (offset:string) (address:string) =
    offset ^ "(" ^ address ^ ")"
  in
  let const (n:int) = string_of_int n in
  let align() = ".align" in
  let header() = ".text\n" in
  let footer() = "\n" in
  let proc_name (name:string) = ".global " ^ name ^ "\n" ^ name ^ ":\n" in
  let branch_link (name:string) = "  blr\n\n" in
  {
    reg_prefix = reg_prefix;
    vec_prefix = vec_prefix;
    vsr_prefix = vsr_prefix;
    maddr      = maddr;
    const      = const;
    align      = align;
    header     = header;
    footer     = footer;
    proc_name  = proc_name;
    ret        = branch_link;
  }
