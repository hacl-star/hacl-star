include "../../arch/x86/vale.i.dfy"
include "../../lib/util/dafny_wrappers.i.dfy"
include "cbc.s.dfy"
include "aes.s.dfy"
include "aes_helpers.i.dfy"

module CBC_Helpers {
import opened x86vale_CBC_temp = x86_vale_i
import opened parser_help_i_CBC_temp = dafny_wrappers_i 
import opened CBCModule_CBC_helpers_tmp = CBCModule
import opened AESModule_CBC_helpers_tmp = AESModule
import opened AESHelpersModule_CBC_helpers_tmp = AESHelpersModule

lemma lemma_CBC_Encrypt_length_specific(key:seq<uint32>, input:seq<Quadword>, alg:Algorithm, IV:Quadword) 
    requires |key| == Nk(alg);
    requires |input| > 0;
    ensures  (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    ensures  (Nb() * (Nr(alg) + 1)) % 4 == 0; 
    ensures  |CBC_Encrypt(key, input, alg, IV)| == |input|;
{
    if |input| == 1 {
    } else {
        lemma_CBC_Encrypt_length_specific(key, input[..|input|-1], alg, IV);
    }
}

lemma lemma_CBC_Encrypt_length(key:seq<uint32>, alg:Algorithm, IV:Quadword) 
    requires |key| == Nk(alg);
    ensures (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    ensures (Nb() * (Nr(alg) + 1)) % 4 == 0; 
    ensures forall input :: |input| > 0 ==> |CBC_Encrypt(key, input, alg, IV)| == |input|;
{
    forall input | |input| > 0
        ensures |CBC_Encrypt(key, input, alg, IV)| == |input|;
    {
        lemma_CBC_Encrypt_length_specific(key, input, alg, IV);
    }
}

function CBC_Encrypt'(key:seq<uint32>, input:seq<Quadword>, alg:Algorithm, IV:Quadword) : seq<Quadword>
    requires |key| == Nk(alg);
    requires |input| > 0;
    ensures  |CBC_Encrypt'(key, input, alg, IV)| == |input|;
{
    lemma_CBC_Encrypt_length_specific(key, input, alg, IV);
    CBC_Encrypt(key, input, alg, IV)
}

predicate InputMatchesMemory(input:seq<Quadword>, mem:Heaplet, input_ptr:int)
    requires mem.QuadwordHeaplet?
{
    forall b:int :: 0 <= b < |input| ==> input_ptr + b*16 in mem.quads 
                                      && mem.quads[input_ptr + b*16].v == input[b]
}

predicate KeyRequirements(key:seq<uint32>, w:seq<uint32>, alg:Algorithm, h:Heaplet, addr:int)
{
       alg == AES_128
    && addr % 16 == 0
    && SeqLength(key) == Nk(alg)
    && Nb() * (Nr(alg) + 1) / 4 == Nr(alg) + 1 
    && Nb() * (Nr(alg) + 1) % 4 == 0
    && SeqLength(w) == 44
    && h.QuadwordHeaplet?
    && (forall j :: 0 <= j <= 10 
                 ==> (addr + j*16) in h.quads 
                  && h.quads[(addr + j*16)].v == Quadword(w[(4 * j)], w[(4 * j + 1)], w[(4 * j + 2)], w[(4 * j + 3)]))
    && KeyExpansionPredicate(key, AES_128, w)
}

predicate CBCOutput(key:seq<uint32>, input:seq<Quadword>, IV:Quadword, alg:Algorithm,
                    mem:Heaplets, id:heaplet_id, output_ptr:int, i:int)
    requires 0 <= i <= |input|;
    requires |key| == Nk(alg);
    requires ValidSrcAddrs(mem, id, output_ptr, 128, Secret, i * 16)
          || ValidSrcAddrs(mem, id, output_ptr, 128, Secret, (i+1) * 16);
{
    forall j:nat :: output_ptr <= output_ptr + j*16 < output_ptr + i*16
            ==> CBC_Encrypt'(key, SeqDrop(input, i), alg, IV)[j] == mem[id].quads[output_ptr + j*16].v
}

predicate CBCOutputFinal(key:seq<uint32>, input:seq<Quadword>, IV:Quadword, alg:Algorithm,
                         mem:Heaplets, id:heaplet_id, output_ptr:int, output:seq<Quadword>)
    requires |key| == Nk(alg);
    requires |input| > 0;
{
    |output| == |input|
 && output == CBC_Encrypt(key, input, alg, IV)
 && forall j :: 0 <= j < |output| 
             ==> ValidSrcAddr(mem, id, output_ptr + j*16, 128, Secret)
              && output[j] == mem[id].quads[output_ptr + j*16].v
}

predicate CBCEncryptBodyPreconditions(
        key:seq<uint32>, w:seq<uint32>, input_id:heaplet_id, input:seq<Quadword>, IV:Quadword, 
        key_id:heaplet_id, alg:Algorithm, output_id:heaplet_id, input_ptr:uint32, output_ptr:uint32, i:nat, 
        eax:uint32, ebx:uint32, ecx:uint32, edx:uint32, 
        mem:Heaplets, xmm0:Quadword) 

{
    // Key requirements from AES128EncryptOneBlock
       ValidSrcAddrs(mem, key_id, eax, 128, Secret, 11 * 16) 
    && KeyRequirements(key, w, alg, mem[key_id], eax)

    // Current input is readable
    && SeqLength(input) > 0 
    && ValidSrcAddr(mem, input_id, ebx, 128, Secret)

    // Restrictions on i
    && 0 <= i < SeqLength(input)

    // Current input in memory matches ghost input
    && mem[input_id].quads[ebx].v == input[i]

    // Current output is writeable
    && ValidDstAddr(mem, output_id, ecx, 128)

    // No overflow
    && ebx + 16 < 4294967296
    && ecx + 16 < 4294967296

    && edx < 0x1_0000_0000

    // Output doesn't overflow
    && output_ptr + |input|*16 < 0x1_0000_0000

    // Framing
    && input_id != key_id 
    && key_id != output_id
    && input_id != output_id

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Everything below is listed not for CBCEncryptBody but to maintain the loop invariants
    ////////////////////////////////////////////////////////////////////////////////////////////////

    // edx is the end of the input
    && edx == input_ptr + |input|*16

    // Input is readable
    && ValidSrcAddrs(mem, input_id, input_ptr, 128, Secret, SeqLength(input) * 16)

    // Input matches ghost sequence
    && InputMatchesMemory(input, mem[input_id], input_ptr)

    // Output is writeable
    && ValidDstAddrs(mem, output_id, output_ptr, 128, SeqLength(input) * 16)

    // Ebx and ecx are properly advanced versions of input and output pointers
    && ebx == input_ptr + i*16
    && ecx == output_ptr + i*16

    // All of the output we've written thus far is readable
    && ValidSrcAddrs(mem, output_id, output_ptr, 128, Secret, i * 16)

    // xmm0 holds the previous CBC value
    && (var rest := if (i == 0) then [IV] else CBC_Encrypt'(key, SeqDrop(input, i), alg, IV);
        xmm0 == last(rest)) 

    // Track the fact that the CBC output is in memory
    && CBCOutput(key, input, IV, alg, mem, output_id, output_ptr, i)
}

lemma lemma_ValidSrcAddrsExtension(old_mem:Heaplets, mem:Heaplets, id:heaplet_id, addr:int, taint:taint, i:nat)
    requires ValidSrcAddrs(old_mem, id, addr, 128, taint, i*16);
    requires ValidSrcAddr(mem, id, addr + i*16, 128, taint);
    requires mem == old_mem[id := old_mem[id].(quads := old_mem[id].quads[addr + i*16 := mem[id].quads[addr + i*16]])];
    ensures  ValidSrcAddrs(mem, id, addr, 128, taint, (i+1)*16);
{
    var num_bytes := (i+1)*16;
//    forall a {:trigger ValidSrcAddr(mem, id, a, 128, taint) } 
//             {:trigger mem[id].quads[a] } 
//             {:trigger a in mem[id].quads }
//        | addr <= a < addr+num_bytes && (a - addr) % 16 == 0 
//        ensures ValidSrcAddr(mem, id, a, 128, taint);
//    {
//        if a < addr + i*16 {
//            assert ValidSrcAddr(old_mem, id, a, 128, taint);
//        } else {
//            assert a == addr + i*16;
//            assert ValidSrcAddr(mem, id, a, 128, taint);
//        }
//    }

}

lemma lemma_CBC_step(key:seq<uint32>, input:seq<Quadword>, IV:Quadword, 
                     alg:Algorithm, i:nat, old_xmm0:Quadword, xmm0:Quadword)
    requires |input| > 0;
    requires i < |input|;
    requires |key| == Nk(alg);
    requires var rest := if (i == 0) then [IV] else CBC_Encrypt'(key, input[..i], alg, IV);
             old_xmm0 == last(rest);
    requires xmm0 == AES_Encrypt(key, QuadwordXor(input[i], old_xmm0), alg);
    ensures  xmm0 == last(CBC_Encrypt'(key, input[..i+1], alg, IV));
{
    if i == 0 {

    } else {
        var rest := if (i == 0) then [IV] else CBC_Encrypt'(key, input[..i], alg, IV);
        var expanded_input := input[..i+1];
        assert |expanded_input| == i + 1;
        var expanded_rest := CBC_Encrypt'(key, all_but_last(expanded_input), alg, IV);

        calc {
            all_but_last(input[..i+1]);
            input[..i+1][..|input[..i+1]|-1];
            input[..i+1][..i+1-1];
            input[..i+1][..i];
            input[..i];
        }

        calc {
            last(expanded_rest);
            last(CBC_Encrypt'(key, all_but_last(expanded_input), alg, IV));
            last(CBC_Encrypt'(key, all_but_last(input[..i+1]), alg, IV));
            last(CBC_Encrypt'(key, input[..i], alg, IV));
            old_xmm0;
        }

        calc {
            last(CBC_Encrypt'(key, input[..i+1], alg, IV));
            last(CBC_Encrypt'(key, expanded_input, alg, IV));
            AES_Encrypt(key, QuadwordXor(last(expanded_input), last(expanded_rest)), alg);
            AES_Encrypt(key, QuadwordXor(input[i], last(expanded_rest)), alg);
            AES_Encrypt(key, QuadwordXor(input[i], last(rest)), alg);
            AES_Encrypt(key, QuadwordXor(input[i], old_xmm0), alg);
            xmm0;
        }
    }
}

lemma lemma_ValidDstAddr(mem:Heaplets, id:heaplet_id, base:int, addr:int, i:int, amount:int)
    requires ValidDstAddrs(mem, id, base, 128, amount*16);
    requires base <= addr < base + amount*16;
    requires addr == base + i*16 + 16;
    //requires (addr - base) % 16 == 0;
    ensures  ValidDstAddr(mem, id, addr, 128);
{
}

lemma lemma_inequality(base:int, i:int, j:int)
    requires base + i * 16 <= base + j*16 < base + (i+1)*16;
    ensures  i == j;
{
    assert i * 16 <= j * 16 < (i+1)*16;
}

lemma lemma_CBCOutputExtension(key:seq<uint32>, input:seq<Quadword>, IV:Quadword, alg:Algorithm,
                               old_mem:Heaplets, mem:Heaplets, id:heaplet_id, output_ptr:int, i:int)
    requires 0 <= i < |input|;
    requires |key| == Nk(alg);
    requires ValidSrcAddrs(old_mem, id, output_ptr, 128, Secret, i * 16);
    requires ValidSrcAddrs(mem, id, output_ptr, 128, Secret, (i+1) * 16);
    requires mem == old_mem[id := mem[id]]
    requires mem[id] == old_mem[id].(quads := old_mem[id].quads[output_ptr + i*16 := QuadwordHeapletEntry(last(CBC_Encrypt'(key, input[..i+1], alg, IV)), Secret)]);
    requires CBCOutput(key, input, IV, alg, old_mem, id, output_ptr, i);
    //requires mem[id].quads[output_ptr + i*16].v == last(CBC_Encrypt'(key, input[..i+1], alg, IV));
    ensures  CBCOutput(key, input, IV, alg, mem, id, output_ptr, i+1);
{
    forall j:nat | output_ptr <= output_ptr + j*16 < output_ptr + (i+1)*16
        ensures CBC_Encrypt'(key, SeqDrop(input, i+1), alg, IV)[j] == mem[id].quads[output_ptr + j*16].v
    {
        if output_ptr + j*16 < output_ptr + i*16 {
            assert j < i;
            if |input| == 1 {
                assert false;
            } else {
                var rest := CBC_Encrypt'(key, all_but_last(SeqDrop(input, i+1)), alg, IV);

                calc {
                    CBC_Encrypt'(key, SeqDrop(input, i+1), alg, IV)[j];
                    (rest + [AES_Encrypt(key, QuadwordXor(last(input), last(rest)), alg)])[j];
                    rest[j];
                        { assert all_but_last(SeqDrop(input, i+1)) == SeqDrop(input, i); }
                    CBC_Encrypt'(key, SeqDrop(input, i), alg, IV)[j];
                }
            }
        } else {
            lemma_inequality(output_ptr, i, j);
            assert i == j;
            calc { 
                CBC_Encrypt'(key, SeqDrop(input, i+1), alg, IV)[j];
                last(CBC_Encrypt'(key, input[..i+1], alg, IV));
                mem[id].quads[output_ptr + j*16].v;
            }
        }
    }
}

predicate {:timeLimitMultiplier 3} CBCEncryptBodyPostconditions(
        key:seq<uint32>, w:seq<uint32>, input_id:heaplet_id, input:seq<Quadword>, IV:Quadword, 
        key_id:heaplet_id, alg:Algorithm, output_id:heaplet_id, input_ptr:uint32, output_ptr:uint32, i:nat, 
        old_eax:uint32, old_ebx:uint32, old_ecx:uint32, old_edx:uint32, 
        eax:uint32, ebx:uint32, ecx:uint32, edx:uint32, 
        old_mem:Heaplets, old_xmm0:Quadword,
        mem:Heaplets, xmm0:Quadword) 
{
    // Key requirements from AES128EncryptOneBlock
       ValidSrcAddrs(mem, key_id, eax, 128, Secret, 11 * 16) 
    && KeyRequirements(key, w, alg, mem[key_id], eax)
    && SeqLength(input) > 0 
    && eax == old_eax

    // edx is the end of the input
    && edx == input_ptr + |input|*16
    && edx < 0x1_0000_0000

    // Output doesn't overflow
    && output_ptr + |input|*16 < 0x1_0000_0000

    // New current input is readable
    //&& (ebx < edx ==> ValidSrcAddr(mem, input_id, ebx, 128, Secret))

    // Restrictions on i
    && 0 <= i < SeqLength(input)
 
    // Output we just wrote is readable
    && ValidSrcAddr(mem, output_id, old_ecx, 128, Secret)

    // Framing -- nothing changed in mem except output_id
    && mem == old_mem[output_id := mem[output_id]]

    // Input was readable
    && ValidSrcAddrs(old_mem, input_id, input_ptr, 128, Secret, SeqLength(input) * 16)

    // Input is still readable
    && ValidSrcAddrs(mem, input_id, input_ptr, 128, Secret, SeqLength(input) * 16)

    // New current input in memory matches ghost input
    //&& (ebx < edx && i + 1 < SeqLength(input) ==> mem[input_id].quads[ebx].v == input[i+1])


    // New output is writeable
    && (ecx < output_ptr + |input|*16 ==> ValidDstAddr(mem, output_id, ecx, 128))

    // No overflow
//    && ebx + 16 < 4294967296
//    && ecx + 16 < 4294967296

    // Framing
    && input_id != key_id 
    && key_id != output_id
    && input_id != output_id

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Everything below is listed not for CBCEncryptBody but to maintain the loop invariants
    ///////////////////////////////////////////////////////////////////////////////////////////

    // Input still matches ghost sequence
    && InputMatchesMemory(input, mem[input_id], input_ptr)

    // Output was writeable
    && ValidDstAddrs(old_mem, output_id, output_ptr, 128, SeqLength(input) * 16)

    // Output is still writeable
    && ValidDstAddrs(mem, output_id, output_ptr, 128, SeqLength(input) * 16)

    // ebx and ecx advanced
    && ebx == old_ebx + 16
    && ecx == old_ecx + 16

    // Ebx and ecx are properly advanced versions of input and output pointers
    && ebx == input_ptr + (i+1)*16
    && ecx == output_ptr + (i+1)*16

    // All of the output we've written thus far is readable
    && ValidSrcAddrs(mem, output_id, output_ptr, 128, Secret, (i+1) * 16)

    // xmm0 holds the previous CBC value
    && xmm0 == last(CBC_Encrypt'(key, input[..i+1], alg, IV))

    // AES semantics
    && (var old_h := old_mem[output_id]; 
        mem[output_id] == old_h.(quads := old_h.quads[old_ecx := QuadwordHeapletEntry(xmm0, Secret)]))
    && xmm0 == AES_Encrypt(key, QuadwordXor(input[i], old_xmm0), alg)

    // Track the fact that the CBC output is in memory
    && CBCOutput(key, input, IV, alg, mem, output_id, output_ptr, i+1)
}

predicate CBCEncryptLoopInvariant(
        key:seq<uint32>, w:seq<uint32>, input_id:heaplet_id, input:seq<Quadword>, IV:Quadword, 
        key_id:heaplet_id, alg:Algorithm, output_id:heaplet_id, input_ptr:uint32, output_ptr:uint32, i:nat, 
        old_eax:uint32, old_ebx:uint32, old_ecx:uint32, old_edx:uint32, 
        eax:uint32, ebx:uint32, ecx:uint32, edx:uint32, 
        old_mem:Heaplets, old_xmm0:Quadword,
        mem:Heaplets, xmm0:Quadword) 
{
    // Key requirements from AES128EncryptOneBlock
       ValidSrcAddrs(mem, key_id, eax, 128, Secret, 11 * 16) 
    && KeyRequirements(key, w, alg, mem[key_id], eax)
    && SeqLength(input) > 0 
    && eax == old_eax

    // edx is the end of the input
    && edx == input_ptr + |input|*16
    && edx < 0x1_0000_0000

    // Ebx and ecx are properly advanced versions of input and output pointers
    && ebx == input_ptr + i*16
    && ecx == output_ptr + i*16

    // Output doesn't overflow
    && output_ptr + |input|*16 < 0x1_0000_0000

    // New current input is readable
    //&& (ebx < edx ==> ValidSrcAddr(mem, input_id, ebx, 128, Secret))

    // Restrictions on i
    && 0 <= i <= |input|
 
    // Output we just wrote is readable
    && (i > 0 ==> ValidSrcAddr(mem, output_id, old_ecx, 128, Secret))

    // Framing -- nothing changed in mem except output_id
    && output_id in mem 
    && mem == old_mem[output_id := mem[output_id]]

//    // Input was readable
//    && ValidSrcAddrs(old_mem, input_id, input_ptr, 128, Secret, SeqLength(input) * 16)

    // Input is still readable
    && ValidSrcAddrs(mem, input_id, input_ptr, 128, Secret, SeqLength(input) * 16)

    // New current input in memory matches ghost input
    //&& (ebx < edx && i + 1 < SeqLength(input) ==> mem[input_id].quads[ebx].v == input[i+1])

    // New output is writeable
    && (ecx < output_ptr + SeqLength(input) * 16 ==> ValidDstAddr(mem, output_id, ecx, 128))

    // Framing
    && input_id != key_id 
    && key_id != output_id
    && input_id != output_id

    // Input matches ghost sequence
    && InputMatchesMemory(input, mem[input_id], input_ptr)

    // Output is writeable
    && ValidDstAddrs(mem, output_id, output_ptr, 128, SeqLength(input) * 16)

    // All of the output we've written thus far is readable
    && ValidSrcAddrs(mem, output_id, output_ptr, 128, Secret, i * 16)

    // AES semantics
    // xmm0 holds the previous CBC value
    && (var rest := if (i == 0) then [IV] else CBC_Encrypt'(key, SeqDrop(input, i), alg, IV);
        xmm0 == last(rest)) 

    // Track the fact that the CBC output is in memory
    && CBCOutput(key, input, IV, alg, mem, output_id, output_ptr, i)
}

lemma CBCEncryptLoopInvariantImpliesPreconditions(
        key:seq<uint32>, w:seq<uint32>, input_id:heaplet_id, input:seq<Quadword>, IV:Quadword, 
        key_id:heaplet_id, alg:Algorithm, output_id:heaplet_id, input_ptr:uint32, output_ptr:uint32, i:nat, 
        old_eax:uint32, old_ebx:uint32, old_ecx:uint32, old_edx:uint32, 
        eax:uint32, ebx:uint32, ecx:uint32, edx:uint32, 
        old_mem:Heaplets, old_xmm0:Quadword,
        mem:Heaplets, xmm0:Quadword) 
    requires ebx < edx;
    requires CBCEncryptLoopInvariant(
                key, w, input_id, input, IV, 
                key_id, alg, output_id, input_ptr, output_ptr, i, 
                old_eax, old_ebx, old_ecx, old_edx,
                eax, ebx, ecx, edx, 
                old_mem, old_xmm0,
                mem, xmm0
             );
    ensures  CBCEncryptBodyPreconditions(
                key, w, input_id, input, IV, 
                key_id, alg, output_id, input_ptr, output_ptr, i, 
                eax, ebx, ecx, edx, 
                mem, xmm0
             );
{
}

lemma CBCEncryptPostconditionsImplyLoopInvariant(
        key:seq<uint32>, w:seq<uint32>, input_id:heaplet_id, input:seq<Quadword>, IV:Quadword, 
        key_id:heaplet_id, alg:Algorithm, output_id:heaplet_id, input_ptr:uint32, output_ptr:uint32, i:nat, 
        old_eax:uint32, old_ebx:uint32, old_ecx:uint32, old_edx:uint32, 
        eax:uint32, ebx:uint32, ecx:uint32, edx:uint32, 
        old_mem:Heaplets, old_xmm0:Quadword,
        mem:Heaplets, xmm0:Quadword) 
    requires old_ebx < old_edx;
    requires CBCEncryptBodyPostconditions(
                key, w, input_id, input, IV, 
                key_id, alg, output_id, input_ptr, output_ptr, i, 
                old_eax, old_ebx, old_ecx, old_edx,
                eax, ebx, ecx, edx, 
                old_mem, old_xmm0,
                mem, xmm0
             );
    ensures  CBCEncryptLoopInvariant(
                key, w, input_id, input, IV, 
                key_id, alg, output_id, input_ptr, output_ptr, i+1, 
                old_eax, old_ebx, old_ecx, old_edx,
                eax, ebx, ecx, edx, 
                old_mem, old_xmm0,
                mem, xmm0
             );
{
//    assert ValidDstAddrs(mem, output_id, output_ptr, 128, SeqLength(input) * 16);
//    if ecx < output_ptr + SeqLength(input)*16 {
////        var j := i+1;
////        calc {
////            ecx - output_ptr;
////            16 * (i+1);
////        }
////        lemma_mod_multiples_vanish(i+1, 0, 16);
////        assert (16*(i+1) + 0) % 16 == 0 % 16 == 0;
////        assert (ecx - output_ptr) % 16 == 0;
////        assert ecx in mem[output_id].quads;
//        assert ValidDstAddr(mem, output_id, ecx, 128);
//    }
//    assume false;
}

lemma {:timeLimitMultiplier 2} lemma_CBCEncryptInvariantImplications(
        key:seq<uint32>, w:seq<uint32>, input_id:heaplet_id, input:seq<Quadword>, IV:Quadword, 
        key_id:heaplet_id, alg:Algorithm, output_id:heaplet_id, input_ptr:uint32, output_ptr:uint32, i:nat, 
        old_eax:uint32, old_ebx:uint32, old_ecx:uint32, old_edx:uint32, 
        eax:uint32, ebx:uint32, ecx:uint32, edx:uint32, 
        old_mem:Heaplets, old_xmm0:Quadword,
        mem:Heaplets, xmm0:Quadword) returns (output:seq<Quadword>)
    requires ebx == edx;
    requires CBCEncryptLoopInvariant(
                key, w, input_id, input, IV, 
                key_id, alg, output_id, input_ptr, output_ptr, i, 
                old_eax, old_ebx, old_ecx, old_edx,
                eax, ebx, ecx, edx, 
                old_mem, old_xmm0,
                mem, xmm0
             );
    //ensures |CBC_Encrypt(key, input, alg, IV)| == |input|;
    ensures CBCOutputFinal(key, input, IV, alg, mem, output_id, output_ptr, output);
{
    calc {
        i*16;
        ebx - input_ptr;
        edx - input_ptr;
        |input|*16;
    }
    assert i == |input|; 
    lemma_CBC_Encrypt_length_specific(key, input, alg, IV);
    assert ValidSrcAddrs(mem, output_id, output_ptr, 128, Secret, i * 16);
    forall j:nat | output_ptr <= output_ptr + j*16 < output_ptr + SeqLength(input)*16
        ensures ValidSrcAddr(mem, output_id, output_ptr + j*16, 128, Secret);
        ensures CBC_Encrypt(key, input, alg, IV)[j] == mem[output_id].quads[output_ptr + j*16].v;
    {
        assert output_ptr <= output_ptr + j*16 < output_ptr + |input|*16;
        calc {
            output_ptr + j*16 - output_ptr;
            j*16;
        }
        assert (j*16) % 16 == 0 by { lemma_mod_multiples_basic(j,16); }
        assert ValidSrcAddr(mem, output_id, output_ptr + j*16, 128, Secret);
        assert CBC_Encrypt'(key, input[..i], alg, IV)[j] == mem[output_id].quads[output_ptr + j*16].v;
        assert input[..i] == input;
    }

    output := CBC_Encrypt(key, input, alg, IV);
    assert forall j :: 0 <= j < |output| 
        ==> ValidSrcAddr(mem, output_id, output_ptr + j*16, 128, Secret)
         && output[j] == mem[output_id].quads[output_ptr + j*16].v;
    assert CBCOutputFinal(key, input, IV, alg, mem, output_id, output_ptr, output);
}


}
