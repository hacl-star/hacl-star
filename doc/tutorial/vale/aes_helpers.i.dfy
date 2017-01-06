include "aes.s.dfy"
include "../../lib/util/operations.i.dfy"
include "../../lib/util/words_and_bytes.i.dfy"
include "../../lib/math/mul.i.dfy"

module AESHelpersModule {

import opened AESModule
import opened operations_i
import opened words_and_bytes_i
import opened Math__mul_i

////////////////////////////////////////////////////////
// MISC LEMMAS
////////////////////////////////////////////////////////

lemma lemma_AES128Size(alg:Algorithm)
    requires alg.AES_128?;
    ensures  Nb() * (Nr(alg) + 1) == 44;
{
    calc {
        Nb() * (Nr(alg) + 1);
        4 * (Nr(alg) + 1);
        4 * 11;
        44;
    }
}

lemma {:timeLimitMultiplier 4} lemma_SubByteInvertsInvSubByte(b:uint8)
    ensures ApplyBox(ApplyBox(b, GetSBox()), GetInvSBox()) == b;
{
    var b' := ApplyBox(b, GetSBox());
    var b'' := ApplyBox(b', GetInvSBox());

    if b < 16 { assert b'' == b; }
    else if b < 32 { assert b'' == b; }
    else if b < 48 { assert b'' == b; }
    else if b < 64 { assert b'' == b; }
    else if b < 80 { assert b'' == b; }
    else if b < 96 { assert b'' == b; }
    else if b < 112 { assert b'' == b; }
    else if b < 128 { assert b'' == b; }
    else if b < 144 { assert b'' == b; }
    else if b < 160 { assert b'' == b; }
    else if b < 176 { assert b'' == b; }
    else if b < 192 { assert b'' == b; }
    else if b < 208 { assert b'' == b; }
    else if b < 224 { assert b'' == b; }
    else if b < 240 { assert b'' == b; }
    else if b <= 255 { assert b'' == b; }
    else { assert false; }
}

lemma lemma_Subsequence<T>(s:seq<T>, t:seq<T>)
    requires |s| >= 11;
    requires t == s[1..10];
    ensures |t| <= |s|;
    ensures |t| == 9;
    ensures forall i {:trigger t[i]} :: 0 <= i < |t| ==> t[i] == s[i+1];
    ensures s[1] == t[0];
    ensures s[2] == t[1];
    ensures s[3] == t[2];
    ensures s[4] == t[3];
    ensures s[5] == t[4];
    ensures s[6] == t[5];
    ensures s[7] == t[6];
    ensures s[8] == t[7];
    ensures s[9] == t[8];
{
}

lemma lemma_RoundKeys(round_keys:seq<Quadword>, w:seq<uint32>, xmm0:Quadword, xmm1:Quadword, xmm2:Quadword, xmm3:Quadword, xmm4:Quadword, xmm5:Quadword, xmm6:Quadword,
                      xmm7:Quadword, xmm8:Quadword, xmm9:Quadword, xmm10:Quadword)
    requires |w| == 44;
    requires round_keys == KeyScheduleWordsToRoundKeys(w);
    requires xmm0  == seq_to_Quadword(w[0..4]);
    requires xmm1  == seq_to_Quadword(w[4..8]);
    requires xmm2  == seq_to_Quadword(w[8..12]);
    requires xmm3  == seq_to_Quadword(w[12..16]);
    requires xmm4  == seq_to_Quadword(w[16..20]);
    requires xmm5  == seq_to_Quadword(w[20..24]);
    requires xmm6  == seq_to_Quadword(w[24..28]);
    requires xmm7  == seq_to_Quadword(w[28..32]);
    requires xmm8  == seq_to_Quadword(w[32..36]);
    requires xmm9  == seq_to_Quadword(w[36..40]);
    requires xmm10 == seq_to_Quadword(w[40..44]);
    ensures  round_keys[0]  == seq_to_Quadword(w[0..4]);
    ensures  round_keys[1]  == seq_to_Quadword(w[4..8]);
    ensures  round_keys[2]  == seq_to_Quadword(w[8..12]);
    ensures  round_keys[3]  == seq_to_Quadword(w[12..16]);
    ensures  round_keys[4]  == seq_to_Quadword(w[16..20]);
    ensures  round_keys[5]  == seq_to_Quadword(w[20..24]);
    ensures  round_keys[6]  == seq_to_Quadword(w[24..28]);
    ensures  round_keys[7]  == seq_to_Quadword(w[28..32]);
    ensures  round_keys[8]  == seq_to_Quadword(w[32..36]);
    ensures  round_keys[9]  == seq_to_Quadword(w[36..40]);
    ensures  round_keys[10] == seq_to_Quadword(w[40..44]);
    ensures  round_keys[0]  == xmm0;
    ensures  round_keys[1]  == xmm1;
    ensures  round_keys[2]  == xmm2;
    ensures  round_keys[3]  == xmm3;
    ensures  round_keys[4]  == xmm4;
    ensures  round_keys[5]  == xmm5;
    ensures  round_keys[6]  == xmm6;
    ensures  round_keys[7]  == xmm7;
    ensures  round_keys[8]  == xmm8;
    ensures  round_keys[9]  == xmm9;
    ensures  round_keys[10] == xmm10;
{
}

lemma lemma_SubsequenceEnd<T>(s:seq<T>)
    requires |s| > 0;
    ensures s[|s|..] == [];
{
}

lemma lemma_RoundsHelper(inp:Quadword, round_keys:seq<Quadword>)
    requires |round_keys| > 0;
    ensures Rounds(inp, round_keys) == Rounds(Round(inp, round_keys[0]), round_keys[1..]);
{
}

lemma lemma_EqInvRoundsHelper(inp:Quadword, round_keys:seq<Quadword>)
    requires |round_keys| > 0;
    ensures EqInvRounds(inp, round_keys) == EqInvRounds(EqInvRound(inp, last(round_keys)), all_but_last(round_keys));
{
}

lemma {:fuel Round,10} lemma_RoundsUnrolling(uint32seq2:Quadword, uint32seq2_round1:Quadword, uint32seq2_round2:Quadword, uint32seq2_round3:Quadword, uint32seq2_round4:Quadword, uint32seq2_round5:Quadword, uint32seq2_round6:Quadword, uint32seq2_round7:Quadword, uint32seq2_round8:Quadword, uint32seq3:Quadword, sub:seq<Quadword>)
    requires |sub| == 9;
    requires uint32seq2_round1 == Round(uint32seq2, sub[0]);
    requires uint32seq2_round2 == Round(uint32seq2_round1, sub[1]);
    requires uint32seq2_round3 == Round(uint32seq2_round2, sub[2]);
    requires uint32seq2_round4 == Round(uint32seq2_round3, sub[3]);
    requires uint32seq2_round5 == Round(uint32seq2_round4, sub[4]);
    requires uint32seq2_round6 == Round(uint32seq2_round5, sub[5]);
    requires uint32seq2_round7 == Round(uint32seq2_round6, sub[6]);
    requires uint32seq2_round8 == Round(uint32seq2_round7, sub[7]);
    requires uint32seq3 == Round(uint32seq2_round8, sub[8]);
    ensures uint32seq3 == Rounds(uint32seq2, sub);
{
    calc {
        uint32seq3;
        Round(Round(Round(Round(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5]), sub[6]), sub[7]), sub[8]);
            { lemma_SubsequenceEnd(sub); }
        Rounds(Round(Round(Round(Round(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5]), sub[6]), sub[7]), sub[8]), sub[9..]);
            { lemma_RoundsHelper(Round(Round(Round(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5]), sub[6]), sub[7]), sub[8..]); }
        Rounds(Round(Round(Round(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5]), sub[6]), sub[7]), sub[8..]);
            { lemma_RoundsHelper(Round(Round(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5]), sub[6]), sub[7..]); }
        Rounds(Round(Round(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5]), sub[6]), sub[7..]);
            { lemma_RoundsHelper(Round(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5]), sub[6..]); }
        Rounds(Round(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5]), sub[6..]);
            { lemma_RoundsHelper(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5..]); }
        Rounds(Round(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4]), sub[5..]);
            { lemma_RoundsHelper(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4..]); }
        Rounds(Round(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3]), sub[4..]);
            { lemma_RoundsHelper(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3..]); }
        Rounds(Round(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2]), sub[3..]);
            { lemma_RoundsHelper(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2..]); }
        Rounds(Round(Round(uint32seq2, sub[0]), sub[1]), sub[2..]);
            { lemma_RoundsHelper(Round(uint32seq2, sub[0]), sub[1..]); }
        Rounds(Round(uint32seq2, sub[0]), sub[1..]);
            { lemma_RoundsHelper(uint32seq2, sub); }
        Rounds(uint32seq2, sub);
    }
}

lemma lemma_AllButLast<T>(s:seq<T>, i:int)
    requires 0 < i < |s|;
    ensures all_but_last(s[0..i]) == s[0..i-1];
{
}

lemma {:fuel EqInvRound,10} lemma_EqInvRoundsUnrolling(uint32seq2:Quadword, uint32seq2_round1:Quadword, uint32seq2_round2:Quadword, uint32seq2_round3:Quadword, uint32seq2_round4:Quadword, uint32seq2_round5:Quadword, uint32seq2_round6:Quadword, uint32seq2_round7:Quadword, uint32seq2_round8:Quadword, uint32seq3:Quadword, sub:seq<Quadword>)
    requires |sub| == 9;
    requires uint32seq2_round1 == EqInvRound(uint32seq2, sub[8]);
    requires uint32seq2_round2 == EqInvRound(uint32seq2_round1, sub[7]);
    requires uint32seq2_round3 == EqInvRound(uint32seq2_round2, sub[6]);
    requires uint32seq2_round4 == EqInvRound(uint32seq2_round3, sub[5]);
    requires uint32seq2_round5 == EqInvRound(uint32seq2_round4, sub[4]);
    requires uint32seq2_round6 == EqInvRound(uint32seq2_round5, sub[3]);
    requires uint32seq2_round7 == EqInvRound(uint32seq2_round6, sub[2]);
    requires uint32seq2_round8 == EqInvRound(uint32seq2_round7, sub[1]);
    requires uint32seq3 == EqInvRound(uint32seq2_round8, sub[0]);
    ensures uint32seq3 == EqInvRounds(uint32seq2, sub);
{
    ghost var temp := EqInvRounds(uint32seq2, sub);
    calc {
        temp;
        EqInvRounds(uint32seq2, sub);
        EqInvRounds(EqInvRound(uint32seq2, last(sub)), all_but_last(sub));
        EqInvRounds(EqInvRound(uint32seq2, sub[8]), sub[0..8]);
        EqInvRounds(EqInvRound(EqInvRound(uint32seq2, sub[8]), last(sub[0..8])), all_but_last(sub[0..8]));
            { assert last(sub[0..8]) == sub[7]; lemma_AllButLast(sub, 8); var i := 8; assert 0 < i < |sub|; assert all_but_last(sub[0..8]) == sub[0..7]; }
        EqInvRounds(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[0..7]);
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), last(sub[0..7])), all_but_last(sub[0..7]));
            { lemma_AllButLast(sub, 7); var i := 7; assert 0 < i < |sub|; assert all_but_last(sub[0..7]) == sub[0..6]; }
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[0..6]);
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), last(sub[0..6])), all_but_last(sub[0..6]));
            { var i := 6; lemma_AllButLast(sub, i); assert 0 < i < |sub|; assert all_but_last(sub[0..6]) == sub[0..5]; }
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[0..5]);
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), last(sub[0..5])), all_but_last(sub[0..5]));
            { var i := 5; lemma_AllButLast(sub, i); assert 0 < i < |sub|; assert all_but_last(sub[0..5]) == sub[0..4]; }
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[0..4]);
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), last(sub[0..4])), all_but_last(sub[0..4]));
            { var i := 4; lemma_AllButLast(sub, i); assert 0 < i < |sub|; assert all_but_last(sub[0..4]) == sub[0..3]; }
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[3]), sub[0..3]);
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[3]), last(sub[0..3])), all_but_last(sub[0..3]));
            { var i := 3; lemma_AllButLast(sub, i); assert 0 < i < |sub|; assert all_but_last(sub[0..3]) == sub[0..2]; }
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[3]), sub[2]), sub[0..2]);
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[3]), sub[2]), last(sub[0..2])), all_but_last(sub[0..2]));
            { var i := 2; lemma_AllButLast(sub, i); assert 0 < i < |sub|; assert all_but_last(sub[0..2]) == sub[0..1]; }
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[3]), sub[2]), sub[1]), sub[0..1]);
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[3]), sub[2]), sub[1]), last(sub[0..1])), all_but_last(sub[0..1]));
            { var i := 1; lemma_AllButLast(sub, i); assert 0 < i < |sub|; assert all_but_last(sub[0..1]) == sub[0..0]; }
        EqInvRounds(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[3]), sub[2]), sub[1]), sub[0]), sub[0..0]);
        EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(EqInvRound(uint32seq2, sub[8]), sub[7]), sub[6]), sub[5]), sub[4]), sub[3]), sub[2]), sub[1]), sub[0]);
        uint32seq3;
    }
    assert temp == uint32seq3;
    assert uint32seq3 == temp;
    assert uint32seq3 == EqInvRounds(uint32seq2, sub);
}

lemma lemma_RotWordSubWordCommutativity(x:uint32)
    ensures RotWord(SubWord(x)) == SubWord(RotWord(x));
{
    ghost var box := GetSBox();

    var x_bytes := WordToBytes(x);
    var rotx_bytes := WordToBytes(BytesToWord(x_bytes[1], x_bytes[2], x_bytes[3], x_bytes[0]));
    var subx_bytes := WordToBytes(SubWord(x));

    calc {
        SubWord(RotWord(x));
        BytesToWord(ApplyBox(rotx_bytes[0], box), ApplyBox(rotx_bytes[1], box), ApplyBox(rotx_bytes[2], box), ApplyBox(rotx_bytes[3], box));
            { lemma_BytesToWord_WordToBytes_inverses(x_bytes[1], x_bytes[2], x_bytes[3], x_bytes[0]);
              assert rotx_bytes == [x_bytes[1], x_bytes[2], x_bytes[3], x_bytes[0]]; }
        BytesToWord(ApplyBox(x_bytes[1], box), ApplyBox(x_bytes[2], box), ApplyBox(x_bytes[3], box), ApplyBox(x_bytes[0], box));
            { lemma_BytesToWord_WordToBytes_inverses(ApplyBox(x_bytes[0], box), ApplyBox(x_bytes[1], box), ApplyBox(x_bytes[2], box), ApplyBox(x_bytes[3], box));
              assert subx_bytes == [ApplyBox(x_bytes[0], box), ApplyBox(x_bytes[1], box), ApplyBox(x_bytes[2], box), ApplyBox(x_bytes[3], box)]; }
        BytesToWord(subx_bytes[1], subx_bytes[2], subx_bytes[3], subx_bytes[0]);
        RotWord(SubWord(x));
    }
}

lemma lemma_Selector255(selector:uint8, bits:BitsOfByte)
    requires selector == 255;
    requires bits == byte_to_bits(selector);
    ensures bits.lo == bits.mid_lo == bits.mid_hi == bits.hi == 3;
{
}

lemma lemma_EqInvKeyExpansionLemma(key:seq<uint32>, alg:Algorithm, w:seq<uint32>, invmixround:seq<uint32>, round:int, index:int, dw:seq<uint32>)
    requires alg == AES_128;
    requires |key| == Nk(alg);
    requires KeyExpansionPredicate(key, alg, w);
    requires |w| == |dw| == 44;

    requires 1 <= round <= 9;
    requires invmixround == Quadword_to_seq(InvMixColumns(seq_to_Quadword(w[4*round..4*round+4])));
    requires index == 4*round;

    requires dw[index] == invmixround[0];
    requires dw[index+1] == invmixround[1];
    requires dw[index+2] == invmixround[2];
    requires dw[index+3] == invmixround[3];

    ensures KeyScheduleWordsToRoundKeys(dw)[round] == InvMixColumns(KeyScheduleWordsToRoundKeys(w)[round]);
{
    var roundSubSeq := w[4*round..4*round+4];
}

////////////////////////////////////////////////////////
// XOR BEHAVIOR
////////////////////////////////////////////////////////

lemma lemma_double_xor_negates(x:uint32, y:uint32, z:uint32)
    ensures BitwiseXor(BitwiseXor(x,y), x) == y;
    ensures BitwiseXor(BitwiseXor(x,y), y) == x;
    ensures BitwiseXor(BitwiseXor(x,y),BitwiseXor(x,z)) == BitwiseXor(y,z);
{
    calc {
        BitwiseXor(BitwiseXor(x,y), x);
            { lemma_BitwiseXorCommutative(BitwiseXor(x, y), x); }
        BitwiseXor(x, BitwiseXor(x,y));
            { lemma_BitwiseXorAssociative(x, x, y); }
        BitwiseXor(BitwiseXor(x,x), y);
            { lemma_BitwiseXorWithItself(x); }
        BitwiseXor(0,y);
            { lemma_BitwiseXorCommutative(0, y); }
        BitwiseXor(y,0);
            { lemma_BitwiseXorWithZero(y); }
        y;
    }

    calc {
        BitwiseXor(BitwiseXor(x,y), y);
            { lemma_BitwiseXorAssociative(x, y, y); }
        BitwiseXor(x, BitwiseXor(y,y));
            { lemma_BitwiseXorWithItself(y); }
        BitwiseXor(x, 0);
            { lemma_BitwiseXorWithZero(x); }
        x;
    }

    calc {
        BitwiseXor(BitwiseXor(x,y), BitwiseXor(x,z));
            { lemma_BitwiseXorAssociative(BitwiseXor(x,y), x, z); }
        BitwiseXor(BitwiseXor(BitwiseXor(x,y),x), z);
        BitwiseXor(y, z);
    }
}

lemma lemma_BitwiseXorAssociative2(x:uint32, y:uint32, z:uint32, p:uint32)
    ensures BitwiseXor(BitwiseXor(x,y), BitwiseXor(z,p)) == BitwiseXor(BitwiseXor(x,z), BitwiseXor(y,p));
{
    calc {
        BitwiseXor(BitwiseXor(x,y), BitwiseXor(z,p));
            { lemma_BitwiseXorAssociative(BitwiseXor(x,y), z, p); }
        BitwiseXor(BitwiseXor(BitwiseXor(x,y), z), p);
            { lemma_BitwiseXorAssociative(x, y, z); }
        BitwiseXor(BitwiseXor(x, BitwiseXor(y,z)), p);
            { lemma_BitwiseXorCommutative(y, z); }
        BitwiseXor(BitwiseXor(x, BitwiseXor(z,y)), p);
            { lemma_BitwiseXorAssociative(x, z, y); }
        BitwiseXor(BitwiseXor(BitwiseXor(x,z), y), p);
            { lemma_BitwiseXorAssociative(BitwiseXor(x,z), y, p); }
        BitwiseXor(BitwiseXor(x,z), BitwiseXor(y,p));
    }
}

////////////////////////////////////////////////////////
// KEY EXPANSION
////////////////////////////////////////////////////////

predicate KeyExpansionPredicateSpecific(key:seq<uint32>, alg:Algorithm, w:seq<uint32>, i:int)
    requires |key| == Nk(alg);
    requires 0 <= i < |w|;
{
    if 0 <= i < Nk(alg) then
        // First Nk elements of the expanded key are the key itself
        w[i] == key[i]
    else if Nk(alg) <= i < Nb() * (Nr(alg) + 1) then
        var temp :=
            if i % Nk(alg) == 0 then
                if 1 <= i / Nk(alg) <= 10 then BitwiseXor(SubWord(RotWord(w[i-1])), AES_Rcon()[ (i / Nk(alg))-1 ]) else 0
            else if Nk(alg) > 6 && i % Nk(alg) == 4 then
                SubWord(w[i-1])
            else  // No update
                w[i-1]
            ;
        w[i] == BitwiseXor(w[i - Nk(alg)], temp)
    else 
        true
}

predicate KeyExpansionPredicatePartial(key:seq<uint32>, alg:Algorithm, w:seq<uint32>, end_index:int) 
    requires |key| == Nk(alg);
    requires end_index <= |w|;
{
    forall i :: 0 <= i < end_index ==> KeyExpansionPredicateSpecific(key, alg, w, i)
}

predicate KeyExpansionPredicate(key:seq<uint32>, alg:Algorithm, w:seq<uint32>) 
    requires |key| == Nk(alg);
{
       |w| == Nb() * (Nr(alg) + 1)
    && KeyExpansionPredicatePartial(key, alg, w, Nb() * (Nr(alg) + 1))
}

lemma lemma_ExpandKeyPartialSatisfiesKeyExpansionPredicatePartial(key:seq<uint32>, alg:Algorithm, w:seq<uint32>, n:int)
    requires |key| == Nk(alg);
    requires 0 <= n <= Nb() * (Nr(alg) + 1);
    requires w == ExpandKeyPartial(key, alg, n);
    ensures  KeyExpansionPredicatePartial(key, alg, w, n);
{
    if n == 0 {
        return;
    }

    var w_prev := ExpandKeyPartial(key, alg, n-1);
    var i := n-1;
    var extra :=
        if 0 <= i < Nk(alg) then
            key[i]
        else
            var temp := 
                if i % Nk(alg) == 0 then
                    // note that the FIPS-197 spec talks about Rcon being 1-indexed, so we have to
                    // subtract 1 from i / Nk(alg)
                    if 1 <= i / Nk(alg) <= 10 then BitwiseXor(SubWord(RotWord(w[i-1])), AES_Rcon()[ (i / Nk(alg))-1 ]) else 0
                else if Nk(alg) > 6 && i % Nk(alg) == 4 then
                    SubWord(w[i-1])
                else  // No update
                    w[i-1];
            BitwiseXor(w[i - Nk(alg)], temp);
    assert w == w_prev + [extra];
    assert w_prev == w[..n-1];
    assert extra == w[n-1];

    lemma_ExpandKeyPartialSatisfiesKeyExpansionPredicatePartial(key, alg, w_prev, n-1);

    forall j | 0 <= j < n
        ensures KeyExpansionPredicateSpecific(key, alg, w, j);
    {
        if j < n-1 {
            assert w[j] == w_prev[j];
            assert KeyExpansionPredicateSpecific(key, alg, w_prev, j);
        }
    }
}

lemma lemma_ExpandKeySatisfiesKeyExpansionPredicate(key:seq<uint32>, alg:Algorithm, w:seq<uint32>)
    requires |key| == Nk(alg);
    requires w == ExpandKey(key, alg);
    ensures  KeyExpansionPredicate(key, alg, w);
{
    lemma_mul_auto();
    lemma_ExpandKeyPartialSatisfiesKeyExpansionPredicatePartial(key, alg, w, Nb() * (Nr(alg) + 1));
}

lemma lemma_KeyExpansionPredicatesMatchAt(key:seq<uint32>, alg:Algorithm, w:seq<uint32>, w':seq<uint32>, i:int)
    requires |key| == Nk(alg);
    requires |w'| == |w| == Nb() * (Nr(alg) + 1);
    requires KeyExpansionPredicate(key, alg, w);
    requires KeyExpansionPredicate(key, alg, w');
    requires 0 <= i < |w|;
    ensures  w[i] == w'[i];
{
    assert KeyExpansionPredicateSpecific(key, alg, w, i);
    assert KeyExpansionPredicateSpecific(key, alg, w', i);
    if 0 <= i < Nk(alg) {
        assert w[i] == key[i] == w'[i];
    }
    else if Nk(alg) <= i < Nb() * (Nr(alg) + 1) {
        lemma_KeyExpansionPredicatesMatchAt(key, alg, w, w', i-1);
        lemma_KeyExpansionPredicatesMatchAt(key, alg, w, w', i-Nk(alg));
        assert w[i] == w'[i];
    }
}

lemma lemma_KeyExpansionPredicateImpliesExpandKey(key:seq<uint32>, alg:Algorithm, w:seq<uint32>)
    requires |key| == Nk(alg);
    requires KeyExpansionPredicate(key, alg, w);
    ensures  w == ExpandKey(key, alg);
{
    var w' := ExpandKey(key, alg);
    lemma_ExpandKeySatisfiesKeyExpansionPredicate(key, alg, w');
    assert |w| == |w'|;
    forall i | 0 <= i < |w|
        ensures w[i] == w'[i];
    {
        lemma_KeyExpansionPredicatesMatchAt(key, alg, w, w', i);
    }
    assert w == w';
}

////////////////////////////////////////////////////////
// EQUIVALENT INVERSE KEY EXPANSION
////////////////////////////////////////////////////////

predicate EqInvKeyExpansionPredicatePartial(key:seq<uint32>, alg:Algorithm, dw:seq<uint32>, max_round:int)
    requires |key| == Nk(alg);
{
       |dw| >= Nb() * (max_round + 1)
    && 0 <= max_round <= Nr(alg)
    && var w := ExpandKey(key, alg);
       lemma_mul_inequality(1, max_round + 1, Nb());
       lemma_mul_is_commutative(Nb(), max_round + 1);
       (forall i :: 0 <= i < Nb() ==> dw[i] == w[i]) // Round-0 keys aren't inverted because they're used in
                                              // the same way in the InvCipher and EqInvCipher routines
    && (forall round :: 1 <= round <= max_round && round < Nr(alg) ==>
             KeyScheduleWordsToRoundKeysPartial(dw, round + 1)[round] 
          == InvMixColumns(KeyScheduleWordsToRoundKeys(w)[round]))
    && (max_round == Nr(alg) ==> forall i :: Nb() * Nr(alg) <= i < Nb() * (Nr(alg) + 1) ==> dw[i] == w[i]) // Round-Nr keys aren't inverted either
}

predicate EqInvKeyExpansionPredicate(key:seq<uint32>, alg:Algorithm, dw:seq<uint32>) 
    requires |key| == Nk(alg);
{
    lemma_mul_inequality(1, Nr(alg) + 1, Nb());
    lemma_mul_is_commutative(Nb(), Nr(alg) + 1);
    var w := ExpandKey(key, alg);
       |dw| == Nb() * (Nr(alg) + 1)
    && (forall i :: 0 <= i < Nb() ==> dw[i] == w[i]) // Round-0 keys aren't inverted because they're used in
                                              // the same way in the InvCipher and EqInvCipher routines
    && (forall round :: 1 <= round < Nr(alg) ==>
             KeyScheduleWordsToRoundKeys(dw)[round] 
          == InvMixColumns(KeyScheduleWordsToRoundKeys(w)[round]))
    && (forall i :: Nb() * Nr(alg) <= i < Nb() * (Nr(alg) + 1) ==> dw[i] == w[i]) // Round-Nr keys aren't inverted either
}

lemma {:timeLimitMultiplier 2} lemma_EqInvExpandKeyPartialSatisfiesEqInvKeyExpansionPredicatePartial(key:seq<uint32>, alg:Algorithm, dw:seq<uint32>, max_round:int)
    requires |key| == Nk(alg);
    requires 0 <= max_round <= Nr(alg);
    requires dw == EqInvExpandKeyPartial(key, alg, max_round);
    ensures  |dw| == Nb() * (max_round+1);
    ensures  EqInvKeyExpansionPredicatePartial(key, alg, dw, max_round);
{
    var w := ExpandKey(key, alg);
    var keywords:seq<uint32> := if 0 <= Nb() * max_round <= Nb() * (max_round + 1) <= |w| then w[Nb() * max_round .. Nb() * (max_round + 1)] else [0, 0, 0, 0];
    lemma_mul_is_commutative(Nb(), max_round);
    lemma_mul_is_commutative(Nb(), max_round + 1);
    lemma_mul_is_commutative(Nb(), Nr(alg) + 1);
    lemma_mul_inequality(max_round, max_round + 1, Nb());
    lemma_mul_inequality(max_round + 1, Nr(alg) + 1, Nb());
    assert 0 <= Nb() * max_round <= Nb() * (max_round + 1) <= |w|;
    assert keywords == w[Nb() * max_round .. Nb() * (max_round + 1)];

    if max_round == 0 {
        return;
    }

    var dw_prev := EqInvExpandKeyPartial(key, alg, max_round-1);
    var extra := if max_round < Nr(alg) then Quadword_to_seq(InvMixColumns(seq_to_Quadword(keywords))) else keywords;
    assert dw == dw_prev + extra;
    lemma_EqInvExpandKeyPartialSatisfiesEqInvKeyExpansionPredicatePartial(key, alg, dw_prev, max_round - 1);

    forall i | 0 <= i < Nb()
        ensures dw[i] == w[i];
    {
        assert dw[i] == dw_prev[i];
    }

    forall round | 1 <= round <= max_round && round < Nr(alg)
        ensures KeyScheduleWordsToRoundKeysPartial(dw, round + 1)[round] == InvMixColumns(KeyScheduleWordsToRoundKeys(w)[round]);
    {
        if round < max_round {
            calc {
                KeyScheduleWordsToRoundKeysPartial(dw, round + 1)[round];
                KeyScheduleWordsToRoundKeysPartial(dw_prev, round + 1)[round];
                InvMixColumns(KeyScheduleWordsToRoundKeys(w)[round]);
            }
        }
    }
}

lemma lemma_EqInvExpandKeySatisfiesEqInvKeyExpansionPredicate(key:seq<uint32>, alg:Algorithm, dw:seq<uint32>)
    requires |key| == Nk(alg);
    requires dw == EqInvExpandKey(key, alg);
    ensures  EqInvKeyExpansionPredicate(key, alg, dw);
{
    lemma_EqInvExpandKeyPartialSatisfiesEqInvKeyExpansionPredicatePartial(key, alg, dw, Nr(alg));
}

lemma lemma_EqInvKeyExpansionPredicatesMatchAt(key:seq<uint32>, alg:Algorithm, dw:seq<uint32>, dw':seq<uint32>, i:int)
    requires |key| == Nk(alg);
    requires EqInvKeyExpansionPredicate(key, alg, dw);
    requires EqInvKeyExpansionPredicate(key, alg, dw');
    requires 0 <= i < |dw|;
    ensures  dw[i] == dw'[i];
{
    var w := ExpandKey(key, alg);

    if 0 <= i < Nb() || Nb() * Nr(alg) <= i < Nb() * (Nr(alg) + 1) {
        assert dw[i] == w[i];
        assert dw'[i] == w[i];
        return;
    }

    assert Nb() <= i < Nb() * Nr(alg);
    var round := i / Nb();
    assert 1 <= round < Nr(alg);

    lemma_mul_is_commutative(Nb(), Nr(alg) + 1);
    assert |dw| % 4 == 0;
    assert KeyScheduleWordsToRoundKeys(dw)[round] == KeyScheduleWordsToRoundKeys(dw')[round];
    assert dw[4*round..4*round+4] == dw'[4*round..4*round+4];

    var which_key := i % Nb();
    assert i == 4*round + which_key;
    assert dw[i] == dw'[i];
}

lemma lemma_EqInvKeyExpansionPredicateImpliesEqInvExpandKey(key:seq<uint32>, alg:Algorithm, dw:seq<uint32>)
    requires |key| == Nk(alg);
    requires EqInvKeyExpansionPredicate(key, alg, dw);
    ensures  dw == EqInvExpandKey(key, alg);
{
    var dw' := EqInvExpandKey(key, alg);
    lemma_EqInvExpandKeySatisfiesEqInvKeyExpansionPredicate(key, alg, dw');
    assert |dw| == |dw'|;
    forall i | 0 <= i < |dw|
        ensures dw[i] == dw'[i];
    {
        lemma_EqInvKeyExpansionPredicatesMatchAt(key, alg, dw, dw', i);
    }
    assert dw == dw';
}

}
