include "../../../arch/arm/vale.i.dfy"
include "../../../arch/arm/globals.s.dfy"
include "../../../arch/arm/nlarith.s.dfy"
include "sha256.i.dfy"
include "bit-vector-lemmas.i.dfy"
include "../../../../obj/arch/arm/decls.gen.dfy"

module sha256_helpers_i {

import opened ARM_vale_i 
import opened globals_s 
import opened sha256_i
import opened bit_vector_lemmas_i
import opened ARM_decls_i
import opened nlarith_s

function{:opaque} OpaqueMod(x:int, y:int):int requires y > 0 { x % y }

function method CheapMod16(j:int) : int
{
    if j < 16 then j 
    else if j < 32 then j - 16 
    else if j < 48 then j - 32 
    else if j < 64 then j - 48 
    else j - 64
}

predicate method Even(i:int) { i % 2 == 0 }

type perm_index = i | 0 <= i < 8
function method ApplyPerm(i:int, perm:perm_index) : int
{
    //if i + perm >= 8 then i + perm - 8 else i + perm
    if i - perm >= 0 then i - perm else i - perm + 8
}

function SelectPerm(arr:seq<uint32>, i:int, perm:perm_index):uint32
    requires |arr| == 8
    requires 0 <= i < 8
{
    arr[if i + perm >= 8 then i + perm - 8 else i + perm]
}

function{:opaque} seq8(a:uint32, b:uint32, c:uint32, d:uint32, e:uint32, f:uint32, g:uint32, h:uint32):seq<uint32>
    ensures (var x := seq8(a, b, c, d, e, f, g, h); |x| == 8 && x[0] == a && x[1] == b && x[2] == c && x[3] == d && x[4] == e && x[5] == f && x[6] == g && x[7] == h)
{
    [a, b, c, d, e, f, g, h]
}

lemma lemma_BitwiseAdd32Associates3'(x1:uint32, x2:uint32, x3:uint32)
    ensures BitwiseAdd32(BitwiseAdd32(x1, x2), x3) == BitwiseAdd32(x1, BitwiseAdd32(x2, x3));
{
    reveal_BitwiseAdd32();
    lemma_AddWrapAssociates(x1, x2, x3);
}

lemma lemma_BitwiseAdd32Associates3(x1:uint32, x2:uint32, x3:uint32)
    ensures BitwiseAdd32(BitwiseAdd32(x1, x2), x3) == BitwiseAdd32(BitwiseAdd32(x1, x3), x2);
{
    calc {
        BitwiseAdd32(BitwiseAdd32(x1, x2), x3);
            { lemma_BitwiseAdd32Associates3'(x1, x2, x3); }
        BitwiseAdd32(x1, BitwiseAdd32(x2, x3));
            { reveal_BitwiseAdd32(); }
        BitwiseAdd32(x1, BitwiseAdd32(x3, x2));
            { lemma_BitwiseAdd32Associates3'(x1, x3, x2); }
        BitwiseAdd32(BitwiseAdd32(x1, x3), x2);
    }
}

lemma lemma_BitwiseAdd32Associates5(x1:uint32, x2:uint32, x3:uint32, x4:uint32, x5:uint32, result:uint32)
    requires result == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x2), x3), x4), x5);
    ensures  result == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x5), x4), x2);
{
    calc {
        result;
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x2), x3), x4), x5);
            { lemma_BitwiseAdd32Associates3(x1, x2, x3); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x2), x4), x5);
            { lemma_BitwiseAdd32Associates3(BitwiseAdd32(x1, x3), x2, x4); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x4), x2), x5);
            { lemma_BitwiseAdd32Associates3(BitwiseAdd32(BitwiseAdd32(x1, x3), x4), x2, x5); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x4), x5), x2);
            { lemma_BitwiseAdd32Associates3(BitwiseAdd32(x1, x3), x4, x5); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x5), x4), x2);
    }
}

lemma lemma_BitwiseAdd32Associates4(x1:uint32, x2:uint32, x3:uint32, x4:uint32, result:uint32)
    requires result == BitwiseAdd32(BitwiseAdd32(x4, BitwiseAdd32(x1, x3)), x2);
    ensures  result == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x2), x3), x4);
{
    calc {
        result ;
        BitwiseAdd32(BitwiseAdd32(x4, BitwiseAdd32(x1, x3)), x2);
            { reveal_BitwiseAdd32(); assert BitwiseAdd32(BitwiseAdd32(x1, x3), x4) == BitwiseAdd32(x4, BitwiseAdd32(x1, x3)); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x4), x2);
            { lemma_BitwiseAdd32Associates3(BitwiseAdd32(x1, x3), x4, x2); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x2), x4);
            { lemma_BitwiseAdd32Associates3(x1, x3, x2); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x2), x3), x4);
    }
}

lemma lemma_Even_properties(i:int)
    ensures Even(i) == !Even(i + 1);
{
}

lemma lemma_perm_properties(i:int, perm:perm_index)
    ensures 0 <= i < 8 ==> ApplyPerm(i, perm) == (i-perm)%8;
{
}

lemma lemma_perm_implications(i:int)
    ensures ApplyPerm(0, (i+1)%8) == ApplyPerm(7, i%8);
    ensures ApplyPerm(1, (i+1)%8) == ApplyPerm(0, i%8);
    ensures ApplyPerm(2, (i+1)%8) == ApplyPerm(1, i%8);
    ensures ApplyPerm(3, (i+1)%8) == ApplyPerm(2, i%8);
    ensures ApplyPerm(4, (i+1)%8) == ApplyPerm(3, i%8);
    ensures ApplyPerm(5, (i+1)%8) == ApplyPerm(4, i%8);
    ensures ApplyPerm(6, (i+1)%8) == ApplyPerm(5, i%8);
    ensures ApplyPerm(7, (i+1)%8) == ApplyPerm(6, i%8);
{
}

lemma lemma_obvious_WordAligned(i:int)
    requires WordAligned(i);
    ensures  WordAligned(i + 4);
{
}

lemma lemma_obvious_mod_with_constants(i:int)
    requires i == 64 || i == 16;
    ensures i % 8 == 0;
{
}

lemma lemma_mod_in_bounds(i:int, base:int, old_val:uint32, val:int)
    requires 0 <= i < 15;
    requires 0 <= base;
    requires old_val == base + (i + 1)*4;
    requires val == BitwiseAdd32(old_val, 4);
    requires base + 16*4 < 0x1_0000_0000;
    ensures  val == base + (i + 2)*4;
{
    reveal_BitwiseAdd32();
    calc {
        val;
        (old_val + 4) % 0x1_0000_0000;
        (base + (i + 1)*4 + 4) % 0x1_0000_0000;
        (base + i*4 + 4 + 4) % 0x1_0000_0000;
        (base + (i+2)*4) % 0x1_0000_0000;
    }
    assert 0 <= base + (i+2) * 4 <= base + 16*4;
}

lemma lemma_mod_in_bounds2(i:int, base:int, old_val:uint32, val:int)
    requires 0 <= i < 64;
    requires 0 <= base;
    requires old_val == base + 4*i;
    requires val == BitwiseAdd32(old_val, 4);
    requires base + 4*64 < 0x1_0000_0000;
    ensures  val == old_val + 4;
    //ensures  val == base + (i + 2)*4;
{
    reveal_BitwiseAdd32();
//    calc {
//        val;
//        (old_val + 4) % 0x1_0000_0000;
//        (base + (i + 1)*4 + 4) % 0x1_0000_0000;
//        (base + i*4 + 4 + 4) % 0x1_0000_0000;
//        (base + (i+2)*4) % 0x1_0000_0000;
//    }
//    assert 0 <= base + (i+2) * 4 <= base + 16*4;
}

lemma lemma_BitwiseAdd32_properties(w:uint32)
    ensures BitwiseAdd32(w, 0) == w;
{ reveal_BitwiseAdd32(); }

lemma lemma_BitwiseAdd32_commutes_forall()
    ensures forall x:uint32, y:uint32 :: BitwiseAdd32(x, y) == BitwiseAdd32(y, x);
{ reveal_BitwiseAdd32(); }

lemma lemma_ValidAddrsPreservation(old_mem:memmap, mem:memmap, base:nat, num_uint32s:nat,
                                   update_addr1:nat, update_addr2:nat)
    requires ValidAddrs(old_mem, base, num_uint32s);
    requires update_addr1 in mem;
    requires update_addr2 in mem;
    requires mem == old_mem[update_addr1 := mem[update_addr1]][update_addr2 := mem[update_addr2]];
    ensures  ValidAddrs(mem, base, num_uint32s);
{
    forall addr | base <= addr < base + num_uint32s*4 && (addr - base) % 4 == 0
        ensures ValidAddr(mem, addr)
    {
        assert ValidAddr(old_mem, addr);
    }
}

lemma lemma_ValidSrcAddrsPreservation(old_mem:memmap, mem:memmap, base:nat, num_uint32s:nat, taint:taint,
                                      update_addr1:nat, update_addr2:nat)
    requires ValidSrcAddrs(old_mem, base, num_uint32s, taint);
    requires update_addr1 in mem;
    requires update_addr2 in mem;
    requires update_addr1 < base || update_addr1 >= base + num_uint32s*4;
    requires update_addr2 < base || update_addr2 >= base + num_uint32s*4;
    requires mem == old_mem[update_addr1 := mem[update_addr1]][update_addr2 := mem[update_addr2]];
    ensures  ValidSrcAddrs(mem, base, num_uint32s, taint);
{
    forall addr | base <= addr < base + num_uint32s*4 && (addr - base) % 4 == 0
        ensures ValidSrcAddr(mem, addr, taint)
    {
        assert ValidSrcAddr(old_mem, addr, taint);
    }
}

lemma lemma_ValidSrcAddrsIncrement(old_mem:memmap, mem:memmap, base:nat, num_uint32s:nat, taint:taint,
                                   step:nat, update_addr1:nat, update_addr2:nat)
    requires 0 <= step < 64;
    requires num_uint32s == 16;
    requires ValidAddrs(old_mem, base, num_uint32s);
    requires ValidSrcAddrs(old_mem, base, (if step < 16 then step else 16), taint);
    requires update_addr1 in mem;
    requires update_addr2 in mem;
    requires update_addr1 < base || update_addr1 >= base + num_uint32s*4;
    requires update_addr2 == base + CheapMod16(step) * 4;
    requires mem == old_mem[update_addr1 := mem[update_addr1]][update_addr2 := mem[update_addr2]];
    requires mem[update_addr2].t == taint;
    ensures ValidSrcAddrs(mem, base, (if step + 1 < 16 then step + 1 else 16), taint);
{
    var i_orig := (if step < 16 then step else 16);
    var i_new := (if step + 1 < 16 then step + 1 else 16);
    forall addr | base <= addr < base + i_new*4 && (addr - base) % 4 == 0
        ensures ValidSrcAddr(mem, addr, taint)
    {
        if addr < update_addr2 {
            assert ValidSrcAddr(old_mem, addr, taint);
            assert ValidSrcAddr(mem, addr, taint);
        } else {
             assert ValidAddr(old_mem, addr);
//            assert update_addr2 <= addr < base + i_new*4;
//            assert base + CheapMod16'(step) * 4 <= addr < base + (if step + 1 < 16 then step + 1 else 16)*4;
//            if step + 1 < 16 {
//                assert base + step * 4 <= addr < base + (step + 1)*4;
//                assert addr == update_addr2;
//                assert i_new <= num_uint32s;
//                assert base <= addr < base + num_uint32s*4 && (addr - base) % 4 == 0;
//                assert ValidAddr(old_mem, addr);
//                assert ValidSrcAddr(mem, addr, taint);
//            } else if step < 16 {
//                assert step == 15;
//                assert base + 15 * 4 <= addr < base + 16*4;
//                assert addr == update_addr2;
//                assert ValidAddr(old_mem, addr);
//                assert ValidSrcAddr(mem, addr, taint);
//            } else {
//                assert step == 16;
//                assert base  <= addr < base + 16*4;
//                assert ValidAddr(old_mem, addr);
//                assert ValidSrcAddr(mem, addr, taint);
//            }
        }
    }
}

predicate InputMatchesMemory(input:seq<uint32>, input_ptr:uint32, num_uint32s:nat, mem:memmap)
    requires ValidAddrs(mem, input_ptr, num_uint32s);
    requires |input| >= num_uint32s;
{
    forall j {:trigger input_ptr+j*4 in mem } :: 0 <= j < num_uint32s ==> mem[input_ptr + j*4].v == input[j]
}

lemma lemma_InputPreservation(old_mem:memmap, mem:memmap, input:seq<uint32>, input_ptr:uint32, num_uint32s:nat,
                              update_addr1:nat, update_addr2:nat)
    requires ValidAddrs(old_mem, input_ptr, num_uint32s);
    requires |input| >= num_uint32s;
    requires InputMatchesMemory(input, input_ptr, num_uint32s, old_mem);
    requires update_addr1 in mem;
    requires update_addr2 in mem;
    requires update_addr1 < input_ptr || update_addr1 >= input_ptr + num_uint32s*4;
    requires update_addr2 < input_ptr || update_addr2 >= input_ptr + num_uint32s*4;
    requires mem == old_mem[update_addr1 := mem[update_addr1]][update_addr2 := mem[update_addr2]];
    ensures  ValidAddrs(mem, input_ptr, num_uint32s);
    ensures  InputMatchesMemory(input, input_ptr, num_uint32s, mem);
{
    lemma_ValidAddrsPreservation(old_mem, mem, input_ptr, num_uint32s, update_addr1, update_addr2);
}

predicate WsMatchMemory(trace:SHA256Trace, i:int, base:uint32, mem:memmap)
        requires 0 <= i <= 64;
        requires |trace.W| > 0;
        requires |last(trace.W)| == 64
        requires ValidAddrs(mem, base, 19);
{
          (i < 16 ==> (forall j :: 0 <= j < i ==> last(trace.W)[j] == mem[base + j*4].v))
 && (16 <= i < 64 ==> (forall j :: i - 16 <= j < i ==> last(trace.W)[j] == mem[base + CheapMod16(j)*4].v))
}

lemma lemma_WsIncrement(old_mem:memmap, mem:memmap, trace1:SHA256Trace, trace2:SHA256Trace, base:uint32,
                        step:nat, update_addr1:nat, update_addr2:nat)
    requires 0 <= step < 64;
    requires |trace1.W| > 0;
    requires |last(trace1.W)| == 64
    requires ValidAddrs(old_mem, base, 19);
    requires |trace2.W| > 0;
    requires last(trace2.W) == last(trace1.W);
    requires ValidAddrs(mem, base, 19);
    requires WsMatchMemory(trace1, step, base, old_mem);
    requires update_addr1 in mem;
    requires update_addr2 in mem;
    requires update_addr1 < base || update_addr1 >= base + 16*4;
    requires update_addr2 == base + CheapMod16(step) * 4;
    requires mem == old_mem[update_addr1 := mem[update_addr1]][update_addr2 := mem[update_addr2]];
    requires mem[update_addr2].v == last(trace1.W)[step];
    ensures  ValidAddrs(mem, base, 19);
    ensures  WsMatchMemory(trace2, step + 1, base, mem);
{
}



}
