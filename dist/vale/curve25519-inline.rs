use std::arch::asm;

/// Computes the addition of four-element f1 with value in f2
/// and returns the carry (if any)
#[inline(always)]
fn add_scalar (out: &mut [u64], f1: &mut [u64], f2: u64) -> () {
  unsafe {
    asm!(
    // Clear registers to propagate the carry bit
    "  xor r8, r8",
    "  xor r9, r9",
    "  xor r10, r10",
    "  xor r11, r11",
    "  xor rax, rax",

    // Begin addition chain
    "  addq 0({f1}), {f2}",
    "  movq {f2}, 0({out})",
    "  adcxq 8({f1}), r8",
    "  movq r8, 8({out})",
    "  adcxq 16({f1}), r9",
    "  movq r9, 16({out})",
    "  adcxq 24({f1}), r10",
    "  movq r10, 24({out})",

    // Return the carry bit in a register
    "  adcx r11, rax",
    f2 = inout(reg) f2 => _,
    out = in(reg) out.as_mut_ptr(),
    f1 = in(reg) f1.as_mut_ptr(),
    out("rax") _,
    out("r8") _,
    out("r9") _,
    out("r10") _,
    out("r11") _,
    );
  }
}

/// Computes the field addition of two field elements
#[inline(always)]
fn fadd (out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> () {
  unsafe {
    asm!(
    // Compute the raw addition of f1 + f2
    "  movq 0({f2}), r8",
    "  addq 0({f1}), r8",
    "  movq 8({f2}), r9",
    "  adcxq 8({f1}), r9",
    "  movq 16({f2}), r10",
    "  adcxq 16({f1}), r10",
    "  movq 24({f2}), r11",
    "  adcxq 24({f1}), r11",

    /////// Wrap the result back into the field ////// 

    // Step 1: Compute carry*38
    "  mov $0, rax",
    "  mov $38, {f2}",
    "  cmovc {f2}, rax",

    // Step 2: Add carry*38 to the original sum
    "  xor rcx, rcx",
    "  add rax, r8",
    "  adcx rcx, r9",
    "  movq r9, 8({out})",
    "  adcx rcx, r10",
    "  movq r10, 16({out})",
    "  adcx rcx, r11",
    "  movq r11, 24({out})",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc {f2}, rax",
    "  add rax, r8",
    "  movq r8, 0({out})",
    f2 = inout(reg) f2.as_mut_ptr() => _,
    out = in(reg) out.as_mut_ptr(),
    f1 = in(reg) f1.as_mut_ptr(),
    out("rax") _,
    out("rcx") _,
    out("r8") _,
    out("r9") _,
    out("r10") _,
    out("r11") _,
    );
  }
}

/// Computes the field substraction of two field elements
#[inline(always)]
fn fsub (out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> () {
  unsafe {
    asm!(
    // Compute the raw substraction of f1-f2
    "  movq 0({f1}), r8",
    "  subq 0({f2}), r8",
    "  movq 8({f1}), r9",
    "  sbbq 8({f2}), r9",
    "  movq 16({f1}), r10",
    "  sbbq 16({f2}), r10",
    "  movq 24({f1}), r11",
    "  sbbq 24({f2}), r11",

    /////// Wrap the result back into the field ////// 

    // Step 1: Compute carry*38
    "  mov $0, rax",
    "  mov $38, rcx",
    "  cmovc rcx, rax",

    // Step 2: Substract carry*38 from the original difference
    "  sub rax, r8",
    "  sbb $0, r9",
    "  sbb $0, r10",
    "  sbb $0, r11",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc rcx, rax",
    "  sub rax, r8",

    // Store the result
    "  movq r8, 0({out})",
    "  movq r9, 8({out})",
    "  movq r10, 16({out})",
    "  movq r11, 24({out})",
    out = in(reg) out.as_mut_ptr(),
    f1 = in(reg) f1.as_mut_ptr(),
    f2 = in(reg) f2.as_mut_ptr(),
    out("rax") _,
    out("rcx") _,
    out("r8") _,
    out("r9") _,
    out("r10") _,
    out("r11") _,
    );
  }
}

/// Computes a field multiplication: out <- f1 * f2
/// Uses the 8-element buffer tmp for intermediate results
#[inline(always)]
fn fmul (out: &mut [u64], f1: &mut [u64], f2: &mut [u64], tmp: &mut [u64]) -> () {
  unsafe {
    asm!(

    /////// Compute the raw multiplication: tmp <- src1 * src2 ////// 

    // Compute src1[0] * src2
    "  movq 0({f1}), rdx",
    "  mulxq 0({f2}), r8, r9",       "  xor r10, r10",     "  movq r8, 0({tmp})",
    "  mulxq 8({f2}), r10, r11",     "  adox r9, r10",     "  movq r10, 8({tmp})",
    "  mulxq 16({f2}), r12, r13",    "  adox r11, r12",
    "  mulxq 24({f2}), r14, rdx",    "  adox r13, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",

    // Compute src1[1] * src2
    "  movq 8({f1}), rdx",
    "  mulxq 0({f2}), r8, r9",       "  xor r10, r10",     "  adcxq 8({tmp}), r8",    "  movq r8, 8({tmp})",
    "  mulxq 8({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 16({tmp})",
    "  mulxq 16({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  mov $0, r8",
    "  mulxq 24({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",


    // Compute src1[2] * src2
    "  movq 16({f1}), rdx",
    "  mulxq 0({f2}), r8, r9",       "  xor r10, r10",    "  adcxq 16({tmp}), r8",    "  movq r8, 16({tmp})",
    "  mulxq 8({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 24({tmp})",
    "  mulxq 16({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  mov $0, r8",
    "  mulxq 24({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",


    // Compute src1[3] * src2
    "  movq 24({f1}), rdx",
    "  mulxq 0({f2}), r8, r9",       "  xor r10, r10",    "  adcxq 24({tmp}), r8",    "  movq r8, 24({tmp})",
    "  mulxq 8({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 32({tmp})",
    "  mulxq 16({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  movq r12, 40({tmp})",    "  mov $0, r8",
    "  mulxq 24({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  movq r14, 48({tmp})",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",     "  movq rax, 56({tmp})",

    // Line up pointers
    "  mov {tmp}, {f1}",
    "  mov {out}, {tmp}",

    /////// Wrap the result back into the field ////// 

    // Step 1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, rdx",
    "  mulxq 32({f1}), r8, r13",
    "  xor {f2}, {f2}",
    "  adoxq 0({f1}), r8",
    "  mulxq 40({f1}), r9, r12",
    "  adcx r13, r9",
    "  adoxq 8({f1}), r9",
    "  mulxq 48({f1}), r10, r13",
    "  adcx r12, r10",
    "  adoxq 16({f1}), r10",
    "  mulxq 56({f1}), r11, rax",
    "  adcx r13, r11",
    "  adoxq 24({f1}), r11",
    "  adcx {f2}, rax",
    "  adox {f2}, rax",
    "  imul rdx, rax",

    // Step 2: Fold the carry back into dst
    "  add rax, r8",
    "  adcx {f2}, r9",
    "  movq r9, 8({tmp})",
    "  adcx {f2}, r10",
    "  movq r10, 16({tmp})",
    "  adcx {f2}, r11",
    "  movq r11, 24({tmp})",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc rdx, rax",
    "  add rax, r8",
    "  movq r8, 0({tmp})",
    f1 = inout(reg) f1.as_mut_ptr() => _,
    f2 = inout(reg) f2.as_mut_ptr() => _,
    tmp = inout(reg) tmp.as_mut_ptr() => _,
    out = in(reg) out.as_mut_ptr(),
    out("rax") _,
    out("rdx") _,
    out("r8") _,
    out("r9") _,
    out("r10") _,
    out("r11") _,
    out("r12") _,
    out("r13") _,
    out("r14") _,
    );
  }
}

/// Computes two field multiplications:
///   out[0] <- f1[0] * f2[0]
///   out[1] <- f1[1] * f2[1]
/// Uses the 16-element buffer tmp for intermediate results:
#[inline(always)]
fn fmul2 (out: &mut [u64], f1: &mut [u64], f2: &mut [u64], tmp: &mut [u64]) -> () {
  unsafe {
    asm!(

    /////// Compute the raw multiplication tmp[0] <- f1[0] * f2[0] ////// 

    // Compute src1[0] * src2
    "  movq 0({f1}), rdx",
    "  mulxq 0({f2}), r8, r9",       "  xor r10, r10",     "  movq r8, 0({tmp})",
    "  mulxq 8({f2}), r10, r11",     "  adox r9, r10",     "  movq r10, 8({tmp})",
    "  mulxq 16({f2}), r12, r13",    "  adox r11, r12",
    "  mulxq 24({f2}), r14, rdx",    "  adox r13, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",

    // Compute src1[1] * src2
    "  movq 8({f1}), rdx",
    "  mulxq 0({f2}), r8, r9",       "  xor r10, r10",     "  adcxq 8({tmp}), r8",    "  movq r8, 8({tmp})",
    "  mulxq 8({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 16({tmp})",
    "  mulxq 16({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  mov $0, r8",
    "  mulxq 24({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",


    // Compute src1[2] * src2
    "  movq 16({f1}), rdx",
    "  mulxq 0({f2}), r8, r9",       "  xor r10, r10",    "  adcxq 16({tmp}), r8",    "  movq r8, 16({tmp})",
    "  mulxq 8({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 24({tmp})",
    "  mulxq 16({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  mov $0, r8",
    "  mulxq 24({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",


    // Compute src1[3] * src2
    "  movq 24({f1}), rdx",
    "  mulxq 0({f2}), r8, r9",       "  xor r10, r10",    "  adcxq 24({tmp}), r8",    "  movq r8, 24({tmp})",
    "  mulxq 8({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 32({tmp})",
    "  mulxq 16({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  movq r12, 40({tmp})",    "  mov $0, r8",
    "  mulxq 24({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  movq r14, 48({tmp})",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",     "  movq rax, 56({tmp})",

    /////// Compute the raw multiplication tmp[1] <- f1[1] * f2[1] ////// 

    // Compute src1[0] * src2
    "  movq 32({f1}), rdx",
    "  mulxq 32({f2}), r8, r9",       "  xor r10, r10",     "  movq r8, 64({tmp})",
    "  mulxq 40({f2}), r10, r11",     "  adox r9, r10",     "  movq r10, 72({tmp})",
    "  mulxq 48({f2}), r12, r13",    "  adox r11, r12",
    "  mulxq 56({f2}), r14, rdx",    "  adox r13, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",

    // Compute src1[1] * src2
    "  movq 40({f1}), rdx",
    "  mulxq 32({f2}), r8, r9",       "  xor r10, r10",     "  adcxq 72({tmp}), r8",    "  movq r8, 72({tmp})",
    "  mulxq 40({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 80({tmp})",
    "  mulxq 48({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  mov $0, r8",
    "  mulxq 56({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",


    // Compute src1[2] * src2
    "  movq 48({f1}), rdx",
    "  mulxq 32({f2}), r8, r9",       "  xor r10, r10",    "  adcxq 80({tmp}), r8",    "  movq r8, 80({tmp})",
    "  mulxq 40({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 88({tmp})",
    "  mulxq 48({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  mov $0, r8",
    "  mulxq 56({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",


    // Compute src1[3] * src2
    "  movq 56({f1}), rdx",
    "  mulxq 32({f2}), r8, r9",       "  xor r10, r10",    "  adcxq 88({tmp}), r8",    "  movq r8, 88({tmp})",
    "  mulxq 40({f2}), r10, r11",     "  adox r9, r10",     "  adcx r12, r10",    "  movq r10, 96({tmp})",
    "  mulxq 48({f2}), r12, r13",    "  adox r11, r12",    "  adcx r14, r12",    "  movq r12, 104({tmp})",    "  mov $0, r8",
    "  mulxq 56({f2}), r14, rdx",    "  adox r13, r14",    "  adcx rax, r14",    "  movq r14, 112({tmp})",    "  mov $0, rax",
                                       "  adox rdx, rax",    "  adcx r8, rax",     "  movq rax, 120({tmp})",

    // Line up pointers
    "  mov {tmp}, {f1}",
    "  mov {out}, {tmp}",

    /////// Wrap the results back into the field ////// 

    // Step 1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, rdx",
    "  mulxq 32({f1}), r8, r13",
    "  xor {f2}, {f2}",
    "  adoxq 0({f1}), r8",
    "  mulxq 40({f1}), r9, r12",
    "  adcx r13, r9",
    "  adoxq 8({f1}), r9",
    "  mulxq 48({f1}), r10, r13",
    "  adcx r12, r10",
    "  adoxq 16({f1}), r10",
    "  mulxq 56({f1}), r11, rax",
    "  adcx r13, r11",
    "  adoxq 24({f1}), r11",
    "  adcx {f2}, rax",
    "  adox {f2}, rax",
    "  imul rdx, rax",

    // Step 2: Fold the carry back into dst
    "  add rax, r8",
    "  adcx {f2}, r9",
    "  movq r9, 8({tmp})",
    "  adcx {f2}, r10",
    "  movq r10, 16({tmp})",
    "  adcx {f2}, r11",
    "  movq r11, 24({tmp})",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc rdx, rax",
    "  add rax, r8",
    "  movq r8, 0({tmp})",

    // Step 1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, rdx",
    "  mulxq 96({f1}), r8, r13",
    "  xor {f2}, {f2}",
    "  adoxq 64({f1}), r8",
    "  mulxq 104({f1}), r9, r12",
    "  adcx r13, r9",
    "  adoxq 72({f1}), r9",
    "  mulxq 112({f1}), r10, r13",
    "  adcx r12, r10",
    "  adoxq 80({f1}), r10",
    "  mulxq 120({f1}), r11, rax",
    "  adcx r13, r11",
    "  adoxq 88({f1}), r11",
    "  adcx {f2}, rax",
    "  adox {f2}, rax",
    "  imul rdx, rax",

    // Step 2: Fold the carry back into dst
    "  add rax, r8",
    "  adcx {f2}, r9",
    "  movq r9, 40({tmp})",
    "  adcx {f2}, r10",
    "  movq r10, 48({tmp})",
    "  adcx {f2}, r11",
    "  movq r11, 56({tmp})",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc rdx, rax",
    "  add rax, r8",
    "  movq r8, 32({tmp})",
    f1 = inout(reg) f1.as_mut_ptr() => _,
    f2 = inout(reg) f2.as_mut_ptr() => _,
    tmp = inout(reg) tmp.as_mut_ptr() => _,
    out = in(reg) out.as_mut_ptr(),
    out("rax") _,
    out("rdx") _,
    out("r8") _,
    out("r9") _,
    out("r10") _,
    out("r11") _,
    out("r12") _,
    out("r13") _,
    out("r14") _,
    );
  }
}

/// Computes the field multiplication of four-element f1 with value in f2
/// Requires f2 to be smaller than 2^17
#[inline(always)]
fn fmul_scalar (out: &mut [u64], f1: &mut [u64], f2: u64) -> () {
  unsafe {
    asm!(
    // Compute the raw multiplication of f1*f2
    "  mulxq 0({f1}), r8, rcx",      // f1[0]*f2
    "  mulxq 8({f1}), r9, r12",      // f1[1]*f2
    "  add rcx, r9",
    "  mov $0, rcx",
    "  mulxq 16({f1}), r10, r13",    // f1[2]*f2
    "  adcx r12, r10",
    "  mulxq 24({f1}), r11, rax",    // f1[3]*f2
    "  adcx r13, r11",
    "  adcx rcx, rax",

    /////// Wrap the result back into the field ////// 

    // Step 1: Compute carry*38
    "  mov $38, rdx",
    "  imul rdx, rax",

    // Step 2: Fold the carry back into dst
    "  add rax, r8",
    "  adcx rcx, r9",
    "  movq r9, 8({out})",
    "  adcx rcx, r10",
    "  movq r10, 16({out})",
    "  adcx rcx, r11",
    "  movq r11, 24({out})",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc rdx, rax",
    "  add rax, r8",
    "  movq r8, 0({out})",
    inout("rdx") f2 => _,
    out = in(reg) out.as_mut_ptr(),
    f1 = in(reg) f1.as_mut_ptr(),
    out("rax") _,
    out("rcx") _,
    out("r8") _,
    out("r9") _,
    out("r10") _,
    out("r11") _,
    out("r12") _,
    out("r13") _,
    );
  }
}

/// Computes p1 <- bit ? p2 : p1 in constant time
#[inline(always)]
fn cswap2 (bit: u64, p1: &mut [u64], p2: &mut [u64]) -> () {
  unsafe {
    asm!(
    // Transfer bit into CF flag
    "  add $18446744073709551615, {bit}",

    // cswap p1[0], p2[0]
    "  movq 0({p1}), r8",
    "  movq 0({p2}), r9",
    "  mov r8, r10",
    "  cmovc r9, r8",
    "  cmovc r10, r9",
    "  movq r8, 0({p1})",
    "  movq r9, 0({p2})",

    // cswap p1[1], p2[1]
    "  movq 8({p1}), r8",
    "  movq 8({p2}), r9",
    "  mov r8, r10",
    "  cmovc r9, r8",
    "  cmovc r10, r9",
    "  movq r8, 8({p1})",
    "  movq r9, 8({p2})",

    // cswap p1[2], p2[2]
    "  movq 16({p1}), r8",
    "  movq 16({p2}), r9",
    "  mov r8, r10",
    "  cmovc r9, r8",
    "  cmovc r10, r9",
    "  movq r8, 16({p1})",
    "  movq r9, 16({p2})",

    // cswap p1[3], p2[3]
    "  movq 24({p1}), r8",
    "  movq 24({p2}), r9",
    "  mov r8, r10",
    "  cmovc r9, r8",
    "  cmovc r10, r9",
    "  movq r8, 24({p1})",
    "  movq r9, 24({p2})",

    // cswap p1[4], p2[4]
    "  movq 32({p1}), r8",
    "  movq 32({p2}), r9",
    "  mov r8, r10",
    "  cmovc r9, r8",
    "  cmovc r10, r9",
    "  movq r8, 32({p1})",
    "  movq r9, 32({p2})",

    // cswap p1[5], p2[5]
    "  movq 40({p1}), r8",
    "  movq 40({p2}), r9",
    "  mov r8, r10",
    "  cmovc r9, r8",
    "  cmovc r10, r9",
    "  movq r8, 40({p1})",
    "  movq r9, 40({p2})",

    // cswap p1[6], p2[6]
    "  movq 48({p1}), r8",
    "  movq 48({p2}), r9",
    "  mov r8, r10",
    "  cmovc r9, r8",
    "  cmovc r10, r9",
    "  movq r8, 48({p1})",
    "  movq r9, 48({p2})",

    // cswap p1[7], p2[7]
    "  movq 56({p1}), r8",
    "  movq 56({p2}), r9",
    "  mov r8, r10",
    "  cmovc r9, r8",
    "  cmovc r10, r9",
    "  movq r8, 56({p1})",
    "  movq r9, 56({p2})",
    bit = inout(reg) bit => _,
    p1 = in(reg) p1.as_mut_ptr(),
    p2 = in(reg) p2.as_mut_ptr(),
    out("r8") _,
    out("r9") _,
    out("r10") _,
    );
  }
}

/// Computes the square of a field element: out <- f * f
/// Uses the 8-element buffer tmp for intermediate results
#[inline(always)]
fn fsqr (out: &mut [u64], f: &mut [u64], tmp: &mut [u64]) -> () {
  unsafe {
    asm!(
    "  push {out}",

    /////// Compute the raw multiplication: tmp <- f * f ////// 

    // Step 1: Compute all partial products
    "  movq 0({f}), rdx",                                       // f[0]
    "  mulxq 8({f}), r8, r14",      "  xor r15, r15",     // f[1]*f[0]
    "  mulxq 16({f}), r9, r10",     "  adcx r14, r9",     // f[2]*f[0]
    "  mulxq 24({f}), rax, rcx",    "  adcx rax, r10",    // f[3]*f[0]
    "  movq 24({f}), rdx",                                      // f[3]
    "  mulxq 8({f}), r11, {out}",     "  adcx rcx, r11",    // f[1]*f[3]
    "  mulxq 16({f}), rax, r13",    "  adcx rax, {out}",    // f[2]*f[3]
    "  movq 8({f}), rdx",             "  adcx r15, r13",    // f1
    "  mulxq 16({f}), rax, rcx",    "  mov $0, r14",        // f[2]*f[1]

    // Step 2: Compute two parallel carry chains
    "  xor r15, r15",
    "  adox rax, r10",
    "  adcx r8, r8",
    "  adox rcx, r11",
    "  adcx r9, r9",
    "  adox r15, {out}",
    "  adcx r10, r10",
    "  adox r15, r13",
    "  adcx r11, r11",
    "  adox r15, r14",
    "  adcx {out}, {out}",
    "  adcx r13, r13",
    "  adcx r14, r14",

    // Step 3: Compute intermediate squares
    "  movq 0({f}), rdx",     "  mulx rdx, rax, rcx",    // f[0]^2
                               "  movq rax, 0({tmp})",
    "  add rcx, r8",       "  movq r8, 8({tmp})",
    "  movq 8({f}), rdx",     "  mulx rdx, rax, rcx",    // f[1]^2
    "  adcx rax, r9",      "  movq r9, 16({tmp})",
    "  adcx rcx, r10",     "  movq r10, 24({tmp})",
    "  movq 16({f}), rdx",    "  mulx rdx, rax, rcx",    // f[2]^2
    "  adcx rax, r11",     "  movq r11, 32({tmp})",
    "  adcx rcx, {out}",     "  movq {out}, 40({tmp})",
    "  movq 24({f}), rdx",    "  mulx rdx, rax, rcx",    // f[3]^2
    "  adcx rax, r13",     "  movq r13, 48({tmp})",
    "  adcx rcx, r14",     "  movq r14, 56({tmp})",

    // Line up pointers
    "  mov {tmp}, {f}",
    "  pop {tmp}",

    /////// Wrap the result back into the field ////// 

    // Step 1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, rdx",
    "  mulxq 32({f}), r8, r13",
    "  xor rcx, rcx",
    "  adoxq 0({f}), r8",
    "  mulxq 40({f}), r9, {out}",
    "  adcx r13, r9",
    "  adoxq 8({f}), r9",
    "  mulxq 48({f}), r10, r13",
    "  adcx {out}, r10",
    "  adoxq 16({f}), r10",
    "  mulxq 56({f}), r11, rax",
    "  adcx r13, r11",
    "  adoxq 24({f}), r11",
    "  adcx rcx, rax",
    "  adox rcx, rax",
    "  imul rdx, rax",

    // Step 2: Fold the carry back into dst
    "  add rax, r8",
    "  adcx rcx, r9",
    "  movq r9, 8({tmp})",
    "  adcx rcx, r10",
    "  movq r10, 16({tmp})",
    "  adcx rcx, r11",
    "  movq r11, 24({tmp})",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc rdx, rax",
    "  add rax, r8",
    "  movq r8, 0({tmp})",
    out = inout(reg) out.as_mut_ptr() => _,
    f = inout(reg) f.as_mut_ptr() => _,
    tmp = inout(reg) tmp.as_mut_ptr() => _,
    out("rax") _,
    out("rcx") _,
    out("rdx") _,
    out("r8") _,
    out("r9") _,
    out("r10") _,
    out("r11") _,
    out("r13") _,
    out("r14") _,
    out("r15") _,
    );
  }
}

/// Computes two field squarings:
///   out[0] <- f[0] * f[0]
///   out[1] <- f[1] * f[1]
/// Uses the 16-element buffer tmp for intermediate results
#[inline(always)]
fn fsqr2 (out: &mut [u64], f: &mut [u64], tmp: &mut [u64]) -> () {
  unsafe {
    asm!(
    "  push {out}",
    // Step 1: Compute all partial products
    "  movq 0({f}), rdx",                                       // f[0]
    "  mulxq 8({f}), r8, r14",      "  xor r15, r15",     // f[1]*f[0]
    "  mulxq 16({f}), r9, r10",     "  adcx r14, r9",     // f[2]*f[0]
    "  mulxq 24({f}), rax, rcx",    "  adcx rax, r10",    // f[3]*f[0]
    "  movq 24({f}), rdx",                                      // f[3]
    "  mulxq 8({f}), r11, {out}",     "  adcx rcx, r11",    // f[1]*f[3]
    "  mulxq 16({f}), rax, r13",    "  adcx rax, {out}",    // f[2]*f[3]
    "  movq 8({f}), rdx",             "  adcx r15, r13",    // f1
    "  mulxq 16({f}), rax, rcx",    "  mov $0, r14",        // f[2]*f[1]

    // Step 2: Compute two parallel carry chains
    "  xor r15, r15",
    "  adox rax, r10",
    "  adcx r8, r8",
    "  adox rcx, r11",
    "  adcx r9, r9",
    "  adox r15, {out}",
    "  adcx r10, r10",
    "  adox r15, r13",
    "  adcx r11, r11",
    "  adox r15, r14",
    "  adcx {out}, {out}",
    "  adcx r13, r13",
    "  adcx r14, r14",

    // Step 3: Compute intermediate squares
    "  movq 0({f}), rdx",     "  mulx rdx, rax, rcx",    // f[0]^2
                               "  movq rax, 0({tmp})",
    "  add rcx, r8",       "  movq r8, 8({tmp})",
    "  movq 8({f}), rdx",     "  mulx rdx, rax, rcx",    // f[1]^2
    "  adcx rax, r9",      "  movq r9, 16({tmp})",
    "  adcx rcx, r10",     "  movq r10, 24({tmp})",
    "  movq 16({f}), rdx",    "  mulx rdx, rax, rcx",    // f[2]^2
    "  adcx rax, r11",     "  movq r11, 32({tmp})",
    "  adcx rcx, {out}",     "  movq {out}, 40({tmp})",
    "  movq 24({f}), rdx",    "  mulx rdx, rax, rcx",    // f[3]^2
    "  adcx rax, r13",     "  movq r13, 48({tmp})",
    "  adcx rcx, r14",     "  movq r14, 56({tmp})",

    // Step 1: Compute all partial products
    "  movq 32({f}), rdx",                                       // f[0]
    "  mulxq 40({f}), r8, r14",      "  xor r15, r15",     // f[1]*f[0]
    "  mulxq 48({f}), r9, r10",     "  adcx r14, r9",     // f[2]*f[0]
    "  mulxq 56({f}), rax, rcx",    "  adcx rax, r10",    // f[3]*f[0]
    "  movq 56({f}), rdx",                                      // f[3]
    "  mulxq 40({f}), r11, {out}",     "  adcx rcx, r11",    // f[1]*f[3]
    "  mulxq 48({f}), rax, r13",    "  adcx rax, {out}",    // f[2]*f[3]
    "  movq 40({f}), rdx",             "  adcx r15, r13",    // f1
    "  mulxq 48({f}), rax, rcx",    "  mov $0, r14",        // f[2]*f[1]

    // Step 2: Compute two parallel carry chains
    "  xor r15, r15",
    "  adox rax, r10",
    "  adcx r8, r8",
    "  adox rcx, r11",
    "  adcx r9, r9",
    "  adox r15, {out}",
    "  adcx r10, r10",
    "  adox r15, r13",
    "  adcx r11, r11",
    "  adox r15, r14",
    "  adcx {out}, {out}",
    "  adcx r13, r13",
    "  adcx r14, r14",

    // Step 3: Compute intermediate squares
    "  movq 32({f}), rdx",     "  mulx rdx, rax, rcx",    // f[0]^2
                               "  movq rax, 64({tmp})",
    "  add rcx, r8",       "  movq r8, 72({tmp})",
    "  movq 40({f}), rdx",     "  mulx rdx, rax, rcx",    // f[1]^2
    "  adcx rax, r9",      "  movq r9, 80({tmp})",
    "  adcx rcx, r10",     "  movq r10, 88({tmp})",
    "  movq 48({f}), rdx",    "  mulx rdx, rax, rcx",    // f[2]^2
    "  adcx rax, r11",     "  movq r11, 96({tmp})",
    "  adcx rcx, {out}",     "  movq {out}, 104({tmp})",
    "  movq 56({f}), rdx",    "  mulx rdx, rax, rcx",    // f[3]^2
    "  adcx rax, r13",     "  movq r13, 112({tmp})",
    "  adcx rcx, r14",     "  movq r14, 120({tmp})",

    // Line up pointers
    "  mov {tmp}, {f}",
    "  pop {tmp}",

    // Step 1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, rdx",
    "  mulxq 32({f}), r8, r13",
    "  xor rcx, rcx",
    "  adoxq 0({f}), r8",
    "  mulxq 40({f}), r9, {out}",
    "  adcx r13, r9",
    "  adoxq 8({f}), r9",
    "  mulxq 48({f}), r10, r13",
    "  adcx {out}, r10",
    "  adoxq 16({f}), r10",
    "  mulxq 56({f}), r11, rax",
    "  adcx r13, r11",
    "  adoxq 24({f}), r11",
    "  adcx rcx, rax",
    "  adox rcx, rax",
    "  imul rdx, rax",

    // Step 2: Fold the carry back into dst
    "  add rax, r8",
    "  adcx rcx, r9",
    "  movq r9, 8({tmp})",
    "  adcx rcx, r10",
    "  movq r10, 16({tmp})",
    "  adcx rcx, r11",
    "  movq r11, 24({tmp})",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc rdx, rax",
    "  add rax, r8",
    "  movq r8, 0({tmp})",

    // Step 1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, rdx",
    "  mulxq 96({f}), r8, r13",
    "  xor rcx, rcx",
    "  adoxq 64({f}), r8",
    "  mulxq 104({f}), r9, {out}",
    "  adcx r13, r9",
    "  adoxq 72({f}), r9",
    "  mulxq 112({f}), r10, r13",
    "  adcx {out}, r10",
    "  adoxq 80({f}), r10",
    "  mulxq 120({f}), r11, rax",
    "  adcx r13, r11",
    "  adoxq 88({f}), r11",
    "  adcx rcx, rax",
    "  adox rcx, rax",
    "  imul rdx, rax",

    // Step 2: Fold the carry back into dst
    "  add rax, r8",
    "  adcx rcx, r9",
    "  movq r9, 40({tmp})",
    "  adcx rcx, r10",
    "  movq r10, 48({tmp})",
    "  adcx rcx, r11",
    "  movq r11, 56({tmp})",

    // Step 3: Fold the carry bit back in; guaranteed not to carry at this point
    "  mov $0, rax",
    "  cmovc rdx, rax",
    "  add rax, r8",
    "  movq r8, 32({tmp})",
    out = inout(reg) out.as_mut_ptr() => _,
    f = inout(reg) f.as_mut_ptr() => _,
    tmp = inout(reg) tmp.as_mut_ptr() => _,
    out("rax") _,
    out("rcx") _,
    out("rdx") _,
    out("r8") _,
    out("r9") _,
    out("r10") _,
    out("r11") _,
    out("r13") _,
    out("r14") _,
    out("r15") _,
    );
  }
}

