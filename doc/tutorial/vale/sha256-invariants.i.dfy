include "../../../arch/arm/vale.i.dfy"
include "../../../arch/arm/globals.s.dfy"
include "sha256.i.dfy"
include "bit-vector-lemmas.i.dfy"
include "../../../../obj/arch/arm/decls.gen.dfy"

module sha256_invariants_i {

import opened sha256_helpers_i_ARM_vale_i = ARM_vale_i 
import opened sha256_helpers_i_globals_s = globals_s 
import opened sha256_helpers_i_sha256_i = sha256_i
import opened sha256_helpers_i_bit_vector_lemmas_i = bit_vector_lemmas_i
import opened sha256_helpers_i_ARM_decls_i = ARM_decls_i 

predicate BlockInvariant(
            trace:SHA256Trace, input:seq<uint32>, globals:map<operand, seq<uint32>>,
            old_M_len:nat, old_mem:memmap, mem:memmap, sp:uint32, lr:uint32, r1:uint32, r12:uint32,
            a:uint32, b:uint32, c:uint32, d:uint32, e:uint32, f:uint32, g:uint32, h:uint32,
            input_taint:taint, input_ptr:uint32, hash_taint:taint, ctx_ptr:uint32, 
            num_blocks:nat, block:nat)
{
 // Stack is accessible
    ValidAddrs(mem, sp, 19)
 && ValidSrcAddr(mem, sp + 16*4, Public) // hash_ptr
 && (block > 0 ==> ValidSrcAddr(mem, sp + 68, Public))   // input_ptr
 && ValidSrcAddr(mem, sp + 72, Public)   // end_ptr

 // Pointer into our in-memory H[8] is valid
 && ctx_ptr == mem[sp + 16 * 4].v
 && (ctx_ptr + 32 < sp || ctx_ptr > sp + 19 * 4)
 && ValidSrcAddrs(mem, ctx_ptr, 8, if block == 0 then hash_taint else input_taint)
 && hash_taint == input_taint

 // Input properties
 && block <= num_blocks
 && |input| == num_blocks*16
 && r1 == input_ptr + block * 16 * 4
 && input_ptr + num_blocks * 16 * 4 == mem[sp + 18*4].v == r12
 && input_ptr + num_blocks * 16 * 4 < 0x1_0000_0000
 && (input_ptr + num_blocks * 16 * 4 < sp || sp + 19 * 4 <= input_ptr)  // Doesn't alias sp
 && (input_ptr + num_blocks * 16 * 4 < ctx_ptr || ctx_ptr + 32 <= input_ptr)  // Doesn't alias input_ptr
 && ValidSrcAddrs(mem, input_ptr, num_blocks * 16, input_taint)
 && (forall j {:trigger input_ptr + j * 4 in mem} :: 0 <= j < num_blocks * 16 ==> mem[input_ptr + j * 4].v == input[j])

 // Trace properties
 && IsCompleteSHA256Trace(trace)
 && SHA256TraceIsCorrect(trace) 
 && |trace.M| == old_M_len + block
 && (forall i :: 0 <= i < block 
             ==> trace.M[old_M_len + i] == bswap32_seq(input[i*16..(i+1)*16])) 

 // Globals properties
 && ValidGlobalsAddr(globals, K_SHA256s().sym, lr) 
 && K_SHA256s() in globals
 && AddressOfGlobal(K_SHA256s()) + 256 < 0x1_0000_0000 
 && lr == AddressOfGlobal(K_SHA256s()) 
 && |globals[K_SHA256s()]| == 256
 && (forall j :: 0 <= j < 64 ==> globals[K_SHA256s()][j] == K_SHA256(j))

 // Hs match memory and our registers
 && last(trace.H)[0] == mem[ctx_ptr + 0 * 4].v == a 
 && last(trace.H)[1] == mem[ctx_ptr + 1 * 4].v == b 
 && last(trace.H)[2] == mem[ctx_ptr + 2 * 4].v == c 
 && last(trace.H)[3] == mem[ctx_ptr + 3 * 4].v == d 
 && last(trace.H)[4] == mem[ctx_ptr + 4 * 4].v == e 
 && last(trace.H)[5] == mem[ctx_ptr + 5 * 4].v == f 
 && last(trace.H)[6] == mem[ctx_ptr + 6 * 4].v == g 
 && last(trace.H)[7] == mem[ctx_ptr + 7 * 4].v == h 

 // Memory framing:  We only touch the stack and 8 bytes pointed to by ctx_ptr
 && (forall addr:uint32 :: addr in old_mem && (addr < sp || addr >= sp + 19 * 4) 
                                         && (addr < ctx_ptr || addr >= ctx_ptr + 8 * 4) 
                     ==> addr in mem && old_mem[addr] == mem[addr])
}

}
