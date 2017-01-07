include "aes_helpers.i.dfy"

module AESLemmasModule {

import opened AESHelpersModule

///////////////////////////////
// TYPES TO USE IN VALE
///////////////////////////////

type QuadwordSeq = seq<Quadword>

///////////////////////////////
// KEY EXPANSION
///////////////////////////////

lemma lemma_KeyExpansionRoundHelperHelper(
    key:seq<uint32>,
    alg:Algorithm,
    w_init:seq<uint32>,
    completedBytes:int,
    xmm1_v9:Quadword,
    important_value:uint32,
    w:seq<uint32>
    )
    requires 4 <= completedBytes <= 40;
    requires alg == AES_128;
    requires |key| == Nk(alg);
    requires |w_init| == Nb() * (Nr(alg) + 1) == 44;
    requires KeyExpansionPredicatePartial(key, alg, w_init, completedBytes);
    requires completedBytes % 4 == 0;
    requires |w| == Nb() * (Nr(alg) + 1);
    requires important_value == BitwiseXor(RotWord(SubWord(w_init[completedBytes-1])), AES_Rcon()[ (completedBytes / Nk(alg))-1 ]);
    requires xmm1_v9.lo == BitwiseXor(w[completedBytes-4], important_value);
    requires xmm1_v9.mid_lo == BitwiseXor(BitwiseXor(w[completedBytes-4], w[completedBytes-3]), important_value);
    requires xmm1_v9.mid_hi == BitwiseXor(BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3])), important_value);
    requires xmm1_v9.hi == BitwiseXor(BitwiseXor(w[completedBytes-1], BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3]))), important_value);
    requires w == w_init[completedBytes := xmm1_v9.lo][completedBytes + 1 := xmm1_v9.mid_lo][completedBytes + 2 := xmm1_v9.mid_hi][completedBytes + 3 := xmm1_v9.hi];
    ensures  KeyExpansionPredicatePartial(key, alg, w, completedBytes+4);
{
    lemma_RotWordSubWordCommutativity(w[completedBytes-1]);
    assert SubWord(RotWord(w[completedBytes-1])) == RotWord(SubWord(w[completedBytes-1]));

    calc {
        w[completedBytes];
        xmm1_v9.lo;
        BitwiseXor(w[completedBytes-4], important_value);
        BitwiseXor(w[completedBytes-4], BitwiseXor(SubWord(RotWord(w[completedBytes-1])), AES_Rcon()[ (completedBytes / Nk(alg))-1 ]));
    }

    calc {
        w[completedBytes+1];
        xmm1_v9.mid_lo;
        BitwiseXor(BitwiseXor(w[completedBytes-4], w[completedBytes-3]), important_value);
            { lemma_BitwiseXorCommutative(w[completedBytes-4], w[completedBytes-3]); }
        BitwiseXor(BitwiseXor(w[completedBytes-3], w[completedBytes-4]), important_value);
            { lemma_BitwiseXorAssociative(w[completedBytes-3], w[completedBytes-4], important_value); }
        BitwiseXor(w[completedBytes-3], BitwiseXor(w[completedBytes-4], important_value));
        BitwiseXor(w[completedBytes-3], w[completedBytes]);
    }

    calc {
        w[completedBytes+2];
        BitwiseXor(BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3])), important_value);
            { lemma_BitwiseXorCommutative(w[completedBytes-4], w[completedBytes-3]); }
        BitwiseXor(BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-3], w[completedBytes-4])), important_value);
            { lemma_BitwiseXorAssociative(w[completedBytes-2], BitwiseXor(w[completedBytes-3], w[completedBytes-4]), important_value); }
        BitwiseXor(w[completedBytes-2], BitwiseXor(BitwiseXor(w[completedBytes-3], w[completedBytes-4]), important_value));
            { lemma_BitwiseXorAssociative(w[completedBytes-3], w[completedBytes-4], important_value); }
        BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-3], BitwiseXor(w[completedBytes-4], important_value)));
        BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-3], w[completedBytes]));
        BitwiseXor(w[completedBytes-2], w[completedBytes+1]);
    }

    calc {
        w[completedBytes+3];
        BitwiseXor(BitwiseXor(w[completedBytes-1], BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3]))), important_value);
            { lemma_BitwiseXorCommutative(w[completedBytes-4], w[completedBytes-3]); }
        BitwiseXor(BitwiseXor(w[completedBytes-1], BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-3], w[completedBytes-4]))), important_value);
            { lemma_BitwiseXorAssociative(w[completedBytes-1], BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-3], w[completedBytes-4])), important_value); }
        BitwiseXor(w[completedBytes-1], BitwiseXor(BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-3], w[completedBytes-4])), important_value));
            { lemma_BitwiseXorCommutative(w[completedBytes-4], w[completedBytes-3]); }
        BitwiseXor(w[completedBytes-1], BitwiseXor(BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3])), important_value));
        BitwiseXor(w[completedBytes-1], w[completedBytes+2]);
    }

    forall i | 0 <= i < completedBytes
        ensures KeyExpansionPredicateSpecific(key, alg, w, i);
    {
        assert KeyExpansionPredicateSpecific(key, alg, w_init, i);
    }
    assert KeyExpansionPredicatePartial(key, alg, w, completedBytes);

    lemma_mod_auto(4);
    assert (completedBytes+1)%4 == 1;
    assert (completedBytes+2)%4 == 2;
    assert (completedBytes+3)%4 == 3;
    assert KeyExpansionPredicatePartial(key, alg, w, completedBytes+4);
}

lemma lemma_KeyExpansionRoundHelper(
    key:seq<uint32>,
    alg:Algorithm,
    w_init:seq<uint32>,
    completedBytes:int,
    xmm1_v0:Quadword,
    xmm2_v1:Quadword,
    xmm2_v2:Quadword,
    xmm3_v3:Quadword,
    xmm1_v4:Quadword,
    xmm3_v5:Quadword,
    xmm1_v6:Quadword,
    xmm3_v7:Quadword,
    xmm1_v8:Quadword,
    xmm1_v9:Quadword,
    w:seq<uint32>
    )
    requires 4 <= completedBytes <= 40;
    requires alg == AES_128;
    requires |key| == Nk(alg);
    requires |w_init| == Nb() * (Nr(alg) + 1) == 44;
    requires KeyExpansionPredicatePartial(key, alg, w_init, completedBytes);
    requires completedBytes % 4 == 0;
    requires |w| == Nb() * (Nr(alg) + 1);
    requires xmm1_v0 == Quadword(w[completedBytes-4], w[completedBytes-3], w[completedBytes-2], w[completedBytes-1]);
    requires var rcon := AES_Rcon()[(completedBytes / Nk(alg)) - 1];
             xmm2_v1 == Quadword(SubWord(xmm1_v0.mid_lo), BitwiseXor(RotWord(SubWord(xmm1_v0.mid_lo)), rcon), SubWord(xmm1_v0.hi), BitwiseXor(RotWord(SubWord(xmm1_v0.hi)), rcon));
    requires var bits := byte_to_bits(255);
             xmm2_v2 == Quadword(select_word(xmm2_v1, bits.lo), select_word(xmm2_v1, bits.mid_lo), select_word(xmm2_v1, bits.mid_hi), select_word(xmm2_v1, bits.hi));
    requires xmm3_v3 == Quadword(0, xmm1_v0.lo, xmm1_v0.mid_lo, xmm1_v0.mid_hi);
    requires xmm1_v4 == QuadwordXor(xmm1_v0, xmm3_v3);
    requires xmm3_v5 == Quadword(0, xmm1_v4.lo, xmm1_v4.mid_lo, xmm1_v4.mid_hi);
    requires xmm1_v6 == QuadwordXor(xmm1_v4, xmm3_v5);
    requires xmm3_v7 == Quadword(0, xmm1_v6.lo, xmm1_v6.mid_lo, xmm1_v6.mid_hi);
    requires xmm1_v8 == QuadwordXor(xmm1_v6, xmm3_v7);
    requires xmm1_v9 == QuadwordXor(xmm1_v8, xmm2_v2);
    requires w == w_init[completedBytes := xmm1_v9.lo][completedBytes + 1 := xmm1_v9.mid_lo][completedBytes + 2 := xmm1_v9.mid_hi][completedBytes + 3 := xmm1_v9.hi];
    ensures  KeyExpansionPredicatePartial(key, alg, w, completedBytes+4);
{
    var important_value := BitwiseXor(RotWord(SubWord(w_init[completedBytes-1])), AES_Rcon()[ (completedBytes / Nk(alg))-1 ]);
    var bits := byte_to_bits(255);
    lemma_Selector255(255, bits);
    calc {
        xmm2_v2.mid_lo;
        select_word(xmm2_v1, bits.mid_lo);
        xmm2_v1.hi;
        important_value;
    }
    calc {
        xmm2_v2.mid_hi;
        select_word(xmm2_v1, bits.mid_hi);
        xmm2_v1.hi;
        important_value;
    }
    lemma_BitwiseXorWithZero(w[completedBytes-4]);
    lemma_BitwiseXorCommutative(w[completedBytes-3], w[completedBytes-4]);
    lemma_double_xor_negates(w[completedBytes-4], w[completedBytes-3], 0);
    lemma_BitwiseXorCommutative(w[completedBytes-2], w[completedBytes-3]);
    lemma_double_xor_negates(w[completedBytes-3], w[completedBytes-2], w[completedBytes-4]);
    calc {
        BitwiseXor(BitwiseXor(w[completedBytes-1], w[completedBytes-2]), BitwiseXor(w[completedBytes-2], w[completedBytes-3]));
            { lemma_BitwiseXorCommutative(w[completedBytes-1], w[completedBytes-2]); }
        BitwiseXor(BitwiseXor(w[completedBytes-2], w[completedBytes-1]), BitwiseXor(w[completedBytes-2], w[completedBytes-3]));
            { lemma_double_xor_negates(w[completedBytes-2], w[completedBytes-1], w[completedBytes-3]); }
        BitwiseXor(w[completedBytes-1], w[completedBytes-3]);
            { lemma_BitwiseXorCommutative(w[completedBytes-1], w[completedBytes-3]); }
        BitwiseXor(w[completedBytes-3], w[completedBytes-1]);
    }
    calc {
        BitwiseXor(BitwiseXor(w[completedBytes-2], w[completedBytes-4]), w[completedBytes-3]);
            { lemma_BitwiseXorAssociative(w[completedBytes-2], w[completedBytes-4], w[completedBytes-3]); }
        BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3]));
    }
    calc {
        BitwiseXor(BitwiseXor(w[completedBytes-3], w[completedBytes-1]), BitwiseXor(w[completedBytes-2], w[completedBytes-4]));
            { lemma_BitwiseXorCommutative(w[completedBytes-3], w[completedBytes-1]); }
        BitwiseXor(BitwiseXor(w[completedBytes-1], w[completedBytes-3]), BitwiseXor(w[completedBytes-2], w[completedBytes-4]));
            { lemma_BitwiseXorAssociative2(w[completedBytes-1], w[completedBytes-3], w[completedBytes-2], w[completedBytes-4]); }
        BitwiseXor(BitwiseXor(w[completedBytes-1], w[completedBytes-2]), BitwiseXor(w[completedBytes-3], w[completedBytes-4]));
        BitwiseXor(BitwiseXor(w[completedBytes-1], w[completedBytes-2]), BitwiseXor(w[completedBytes-4], w[completedBytes-3]));
            { lemma_BitwiseXorAssociative(w[completedBytes-1], w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3])); }
        BitwiseXor(w[completedBytes-1], BitwiseXor(w[completedBytes-2], BitwiseXor(w[completedBytes-4], w[completedBytes-3])));
    }
    lemma_KeyExpansionRoundHelperHelper(key, alg, w_init, completedBytes, xmm1_v9, important_value, w);
}

////////////////////////////////////////
// EQUIVALENT-INVERSE KEY EXPANSION
////////////////////////////////////////

lemma {:timeLimitMultiplier 3} lemma_KeyInversionRoundHelper(
    completed_words:int,
    key:seq<uint32>,
    w:seq<uint32>,
    dw:seq<uint32>,
    dw':seq<uint32>
    )
    requires |key| == 4;
    requires 1 <= completed_words <= 9;
    requires KeyExpansionPredicate(key, AES_128, w);
    requires EqInvKeyExpansionPredicatePartial(key, AES_128, dw, completed_words-1);
    requires |dw| == 4 * completed_words;
    requires dw' == dw + Quadword_to_seq(InvMixColumns(seq_to_Quadword(w[4*completed_words..4*(completed_words+1)])));
    ensures  EqInvKeyExpansionPredicatePartial(key, AES_128, dw', completed_words);
    ensures  |dw'| == 4 * (completed_words + 1);
{
    lemma_KeyExpansionPredicateImpliesExpandKey(key, AES_128, w);
}

///////////////////////////////
// ENCRYPTION
///////////////////////////////

predicate IsValidAES128EncryptionTracePrefix(key:seq<uint32>, w:seq<uint32>, input:Quadword, trace:QuadwordSeq)
{
       |key| == 4
    && |w| == 44
    && KeyExpansionPredicate(key, AES_128, w)
    && |trace| <= 11
    && forall i {:trigger w[4*i..4*i+4]} :: 0 <= i < |trace| ==> trace[i] ==
           var ws := seq_to_Quadword(w[4*i..4*i+4]);
           (if i == 0 then QuadwordXor(input, ws)
             else if i < 10 then QuadwordXor(MixColumns(SubBytes(ShiftRows(trace[i-1]))), ws)
             else QuadwordXor(SubBytes(ShiftRows(trace[i-1])), ws))
}

lemma {:timeLimitMultiplier 3} lemma_ExtendingAES128EncryptionTracePrefix(
    key:seq<uint32>,
    w:seq<uint32>,
    input:Quadword,
    round:int,
    old_xmm1:Quadword,
    new_xmm1:Quadword,
    trace:QuadwordSeq,
    trace':QuadwordSeq
    )
    requires IsValidAES128EncryptionTracePrefix(key, w, input, trace);
    requires 1 <= round <= 10;
    requires |trace| == round;
    requires last(trace) == old_xmm1;
    requires trace' == trace + [new_xmm1];
    requires var ws := seq_to_Quadword(w[4*round..4*round+4]);
             new_xmm1 == if round < 10 then QuadwordXor(MixColumns(SubBytes(ShiftRows(trace[round-1]))), ws) else QuadwordXor(SubBytes(ShiftRows(trace[round-1])), ws);
    ensures  IsValidAES128EncryptionTracePrefix(key, w, input, trace');
{
}

lemma lemma_AES128EncryptRound(xmm:Quadword, inputxmm_start:Quadword, inputxmm_end:Quadword, qw_start:Quadword, qw_end:Quadword, round_keys:seq<Quadword>, index:int)
    requires inputxmm_end == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_start))), xmm);
    requires qw_start == inputxmm_start;
    requires qw_end == inputxmm_end;
    requires |round_keys| >= 11;
    requires 0 <= index < |round_keys|;
    requires round_keys[index] == xmm;
    ensures  qw_end == Round(qw_start, round_keys[index]);
{
    SubBytesShiftRowsCommutativity(qw_start);
}

lemma {:timeLimitMultiplier 2} lemma_AES128EncryptRaw(key:seq<uint32>, input:Quadword, alg:Algorithm, w:seq<uint32>, s:Quadword, xmm0:Quadword, xmm1:Quadword, xmm2:Quadword, xmm3:Quadword, xmm4:Quadword, xmm5:Quadword, xmm6:Quadword, xmm7:Quadword, xmm8:Quadword, xmm9:Quadword, xmm10:Quadword, inputxmm_v1:Quadword, inputxmm_v2:Quadword, inputxmm_v3:Quadword, inputxmm_v4:Quadword, inputxmm_v5:Quadword, inputxmm_v6:Quadword, inputxmm_v7:Quadword, inputxmm_v8:Quadword, inputxmm_v9:Quadword, inputxmm_v10:Quadword, inputxmm_v11:Quadword, inputxmm_v12:Quadword)
    requires alg == AES_128;
    requires |key| == Nk(alg);
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to Cipher
    requires w == ExpandKey(key, alg);
    requires |w| == 44;
    requires xmm0 == seq_to_Quadword(w[0..4]);
    requires xmm1 == seq_to_Quadword(w[4..8]);
    requires xmm2 == seq_to_Quadword(w[8..12]);
    requires xmm3 == seq_to_Quadword(w[12..16]);
    requires xmm4 == seq_to_Quadword(w[16..20]);
    requires xmm5 == seq_to_Quadword(w[20..24]);
    requires xmm6 == seq_to_Quadword(w[24..28]);
    requires xmm7 == seq_to_Quadword(w[28..32]);
    requires xmm8 == seq_to_Quadword(w[32..36]);
    requires xmm9 == seq_to_Quadword(w[36..40]);
    requires xmm10 == seq_to_Quadword(w[40..44]);
    requires inputxmm_v1 == input;
    requires inputxmm_v2  == QuadwordXor(inputxmm_v1, xmm0);
    requires inputxmm_v3  == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v2))),  xmm1);
    requires inputxmm_v4  == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v3))),  xmm2);
    requires inputxmm_v5  == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v4))),  xmm3);
    requires inputxmm_v6  == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v5))),  xmm4);
    requires inputxmm_v7  == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v6))),  xmm5);
    requires inputxmm_v8  == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v7))),  xmm6);
    requires inputxmm_v9  == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v8))),  xmm7);
    requires inputxmm_v10 == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v9))),  xmm8);
    requires inputxmm_v11 == QuadwordXor(MixColumns(SubBytes(ShiftRows(inputxmm_v10))), xmm9);
    requires inputxmm_v12 == QuadwordXor(SubBytes(ShiftRows(inputxmm_v11)), xmm10);
    requires s == inputxmm_v12; 
    ensures s == AES_Encrypt(key, input, alg);
{
    lemma_ExpandKeySatisfiesKeyExpansionPredicate(key, alg, w);
    ghost var round_keys := KeyScheduleWordsToRoundKeys(w);

    lemma_RoundKeys(round_keys, w, xmm0, xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7, xmm8, xmm9, xmm10);

    ghost var sub := round_keys[1..10];

    lemma_Subsequence(round_keys, sub);

    assert inputxmm_v2 == QuadwordXor(inputxmm_v1, round_keys[0]);

    ghost var temparg := MixColumns(SubBytes(ShiftRows(inputxmm_v2)));
    calc {
        temparg;
        MixColumns(SubBytes(ShiftRows(inputxmm_v2)));
            { SubBytesShiftRowsCommutativity(inputxmm_v2); assert SubBytes(ShiftRows(inputxmm_v2)) == ShiftRows(SubBytes(inputxmm_v2)); }
        MixColumns(ShiftRows(SubBytes(inputxmm_v2)));
    }
    ghost var k := 0;
    assert 0 <= k < |sub|;
    assert sub != [];

    SubBytesShiftRowsCommutativity(inputxmm_v2);
    SubBytesShiftRowsCommutativity(inputxmm_v3);
    SubBytesShiftRowsCommutativity(inputxmm_v4);
    SubBytesShiftRowsCommutativity(inputxmm_v5);
    SubBytesShiftRowsCommutativity(inputxmm_v6);
    SubBytesShiftRowsCommutativity(inputxmm_v7);
    SubBytesShiftRowsCommutativity(inputxmm_v8);
    SubBytesShiftRowsCommutativity(inputxmm_v9);
    SubBytesShiftRowsCommutativity(inputxmm_v10);

    lemma_AES128EncryptRound(xmm1, inputxmm_v2, inputxmm_v3, inputxmm_v2, inputxmm_v3, round_keys, 1);

    lemma_RoundsUnrolling(inputxmm_v2, inputxmm_v3, inputxmm_v4, inputxmm_v5, inputxmm_v6,
                    inputxmm_v7, inputxmm_v8, inputxmm_v9, inputxmm_v10, inputxmm_v11, sub);

    ghost var qw5 := ShiftRows(SubBytes(inputxmm_v11));

    SubBytesShiftRowsCommutativity(inputxmm_v11);

    ghost var qw6 := AddRoundKey(qw5, round_keys[Nr(alg)]);
    ghost var temp := round_keys[10];
    calc {
        qw6;
        AddRoundKey(qw5, round_keys[Nr(alg)]);
        AddRoundKey(ShiftRows(SubBytes(inputxmm_v11)), round_keys[Nr(alg)]);
        AddRoundKey(ShiftRows(SubBytes(Rounds(inputxmm_v2, round_keys[1..Nr(alg)]))), round_keys[Nr(alg)]);
        AddRoundKey(ShiftRows(SubBytes(Rounds(AddRoundKey(inputxmm_v1, round_keys[0]), round_keys[1..Nr(alg)]))), round_keys[Nr(alg)]);
        AddRoundKey(ShiftRows(SubBytes(Rounds(AddRoundKey(input, round_keys[0]), round_keys[1..Nr(alg)]))), round_keys[Nr(alg)]);
    }
}

lemma {:timeLimitMultiplier 3} lemma_AES128Encrypt(
    key:seq<uint32>,
    input:Quadword,
    w:seq<uint32>,
    s:Quadword,
    trace:QuadwordSeq
    )
    requires IsValidAES128EncryptionTracePrefix(key, w, input, trace);
    requires KeyExpansionPredicate(key, AES_128(), w);
    requires |trace| == 11;
    requires s == last(trace);
    ensures  s == AES_Encrypt(key, input, AES_128());
{
    lemma_KeyExpansionPredicateImpliesExpandKey(key, AES_128(), w);
    lemma_AES128EncryptRaw(key, input, AES_128(), w, s,
                           seq_to_Quadword(w[4*0..4*0+4]),
                           seq_to_Quadword(w[4*1..4*1+4]),
                           seq_to_Quadword(w[4*2..4*2+4]),
                           seq_to_Quadword(w[4*3..4*3+4]),
                           seq_to_Quadword(w[4*4..4*4+4]),
                           seq_to_Quadword(w[4*5..4*5+4]),
                           seq_to_Quadword(w[4*6..4*6+4]),
                           seq_to_Quadword(w[4*7..4*7+4]),
                           seq_to_Quadword(w[4*8..4*8+4]),
                           seq_to_Quadword(w[4*9..4*9+4]),
                           seq_to_Quadword(w[4*10..4*10+4]),
                           input,
                           trace[0], trace[1], trace[2], trace[3], trace[4], trace[5], trace[6], trace[7], trace[8], trace[9], trace[10]);
}

///////////////////////////////
// DECRYPTION
///////////////////////////////

predicate IsValidAES128DecryptionTracePrefix(key:seq<uint32>, dw:seq<uint32>, input:Quadword, trace:QuadwordSeq)
{
       |key| == 4
    && |dw| == 44
    && EqInvKeyExpansionPredicate(key, AES_128, dw)
    && |trace| <= 11
    && forall i {:trigger dw[4*(10-i)..4*(10-i)+4]} :: 0 <= i < |trace| ==> trace[i] ==
           var dws := seq_to_Quadword(dw[4*(10-i)..4*(10-i)+4]);
           (if i == 0 then QuadwordXor(input, dws)
             else if i < 10 then QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(trace[i-1]))), dws)
             else QuadwordXor(InvSubBytes(InvShiftRows(trace[i-1])), dws))
}

lemma {:timeLimitMultiplier 2} lemma_ExtendingAES128DecryptionTracePrefix(
    key:seq<uint32>,
    dw:seq<uint32>,
    input:Quadword,
    round:int,
    old_xmm1:Quadword,
    new_xmm1:Quadword,
    trace:QuadwordSeq,
    trace':QuadwordSeq
    )
    requires IsValidAES128DecryptionTracePrefix(key, dw, input, trace);
    requires 1 <= round <= 10;
    requires |trace| == round;
    requires last(trace) == old_xmm1;
    requires trace' == trace + [new_xmm1];
    requires var dws := seq_to_Quadword(dw[4*(10-round)..4*(10-round)+4]);
             new_xmm1 == if round < 10 then QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(trace[round-1]))), dws) else QuadwordXor(InvSubBytes(InvShiftRows(trace[round-1])), dws);
    ensures  IsValidAES128DecryptionTracePrefix(key, dw, input, trace');
{
}

lemma AES128Decrypt_InvRound(xmm:Quadword, inputxmm_start:Quadword, inputxmm_end:Quadword, qw_start:Quadword, qw_end:Quadword, round_keys:seq<Quadword>, index:int)
    requires inputxmm_end == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_start))), xmm);
    requires qw_start == inputxmm_start;
    requires qw_end   == inputxmm_end;
    requires |round_keys| >= 11;
    requires 0 <= index < |round_keys|;
    requires round_keys[index] == xmm;
    ensures  qw_end == EqInvRound(qw_start, round_keys[index]);
{

    InvSubBytesInvShiftRowsCommutativity(qw_start);
}

lemma {:timeLimitMultiplier 2} lemma_AES128DecryptRaw(key:seq<uint32>, input:Quadword, alg:Algorithm, dw:seq<uint32>, s:Quadword, xmm0:Quadword, xmm1:Quadword, xmm2:Quadword, xmm3:Quadword, xmm4:Quadword, xmm5:Quadword, xmm6:Quadword, xmm7:Quadword, xmm8:Quadword, xmm9:Quadword, xmm10:Quadword, inputxmm_v1:Quadword, inputxmm_v2:Quadword, inputxmm_v3:Quadword, inputxmm_v4:Quadword, inputxmm_v5:Quadword, inputxmm_v6:Quadword, inputxmm_v7:Quadword, inputxmm_v8:Quadword, inputxmm_v9:Quadword, inputxmm_v10:Quadword, inputxmm_v11:Quadword, inputxmm_v12:Quadword)
    requires alg == AES_128;
    requires |key| == Nk(alg);
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to Cipher
    requires dw == EqInvExpandKey(key, alg);
    requires |dw| == 44;
    requires xmm0 == seq_to_Quadword(dw[0..4]);
    requires xmm1 == seq_to_Quadword(dw[4..8]);
    requires xmm2 == seq_to_Quadword(dw[8..12]);
    requires xmm3 == seq_to_Quadword(dw[12..16]);
    requires xmm4 == seq_to_Quadword(dw[16..20]);
    requires xmm5 == seq_to_Quadword(dw[20..24]);
    requires xmm6 == seq_to_Quadword(dw[24..28]);
    requires xmm7 == seq_to_Quadword(dw[28..32]);
    requires xmm8 == seq_to_Quadword(dw[32..36]);
    requires xmm9 == seq_to_Quadword(dw[36..40]);
    requires xmm10 == seq_to_Quadword(dw[40..44]);
    requires inputxmm_v1  == input;
    requires inputxmm_v2  == QuadwordXor(inputxmm_v1, xmm10);
    requires inputxmm_v3  == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v2))),  xmm9);
    requires inputxmm_v4  == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v3))),  xmm8);
    requires inputxmm_v5  == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v4))),  xmm7);
    requires inputxmm_v6  == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v5))),  xmm6);
    requires inputxmm_v7  == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v6))),  xmm5);
    requires inputxmm_v8  == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v7))),  xmm4);
    requires inputxmm_v9  == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v8))),  xmm3);
    requires inputxmm_v10 == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v9))),  xmm2);
    requires inputxmm_v11 == QuadwordXor(InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v10))), xmm1);
    requires inputxmm_v12 == QuadwordXor(InvSubBytes(InvShiftRows(inputxmm_v11)), xmm0);
    requires s == inputxmm_v12;
    ensures s == AES_EquivDecrypt(key, input, alg);
{
    lemma_EqInvExpandKeySatisfiesEqInvKeyExpansionPredicate(key, alg, dw);
    ghost var round_keys := KeyScheduleWordsToRoundKeys(dw);

    lemma_RoundKeys(round_keys, dw, xmm0, xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7, xmm8, xmm9, xmm10);

    ghost var sub := round_keys[1..10];

    lemma_Subsequence(round_keys, sub);

    ghost var qw1 := inputxmm_v1;
    ghost var qw2 := inputxmm_v2;
    ghost var temparg := InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v2)));
    calc {
        temparg;
        InvMixColumns(InvSubBytes(InvShiftRows(inputxmm_v2)));
            { InvSubBytesInvShiftRowsCommutativity(inputxmm_v2); assert InvSubBytes(InvShiftRows(inputxmm_v2)) == InvShiftRows(InvSubBytes(inputxmm_v2)); }
        InvMixColumns(InvShiftRows(InvSubBytes(inputxmm_v2)));
    }
    InvSubBytesInvShiftRowsCommutativity(qw2);
    InvSubBytesInvShiftRowsCommutativity(inputxmm_v3);
    InvSubBytesInvShiftRowsCommutativity(inputxmm_v4);
    InvSubBytesInvShiftRowsCommutativity(inputxmm_v5);
    InvSubBytesInvShiftRowsCommutativity(inputxmm_v6);
    InvSubBytesInvShiftRowsCommutativity(inputxmm_v7);
    InvSubBytesInvShiftRowsCommutativity(inputxmm_v8);
    InvSubBytesInvShiftRowsCommutativity(inputxmm_v9);
    InvSubBytesInvShiftRowsCommutativity(inputxmm_v10);

    AES128Decrypt_InvRound(xmm9, inputxmm_v2, inputxmm_v3, qw2, inputxmm_v3, round_keys, 9);
    AES128Decrypt_InvRound(xmm1, inputxmm_v10, inputxmm_v11, inputxmm_v10, inputxmm_v11, round_keys, 1);

    lemma_EqInvRoundsUnrolling(qw2, inputxmm_v3, inputxmm_v4, inputxmm_v5, inputxmm_v6,
                    inputxmm_v7, inputxmm_v8, inputxmm_v9, inputxmm_v10, inputxmm_v11, sub);

    ghost var qw5 := InvShiftRows(InvSubBytes(inputxmm_v11));

    InvSubBytesInvShiftRowsCommutativity(inputxmm_v11);
}

lemma {:timeLimitMultiplier 2} lemma_AES128Decrypt(
    key:seq<uint32>,
    input:Quadword,
    dw:seq<uint32>,
    s:Quadword,
    trace:QuadwordSeq
    )
    requires IsValidAES128DecryptionTracePrefix(key, dw, input, trace);
    requires EqInvKeyExpansionPredicate(key, AES_128(), dw);
    requires |trace| == 11;
    requires s == last(trace);
    ensures  s == AES_EquivDecrypt(key, input, AES_128());
{
    lemma_EqInvKeyExpansionPredicateImpliesEqInvExpandKey(key, AES_128(), dw);

    assert dw[4*(10-0)..4*(10-0)+4] == dw[40..44];
    assert dw[4*(10-1)..4*(10-1)+4] == dw[36..40];
    assert dw[4*(10-2)..4*(10-2)+4] == dw[32..36];
    assert dw[4*(10-3)..4*(10-3)+4] == dw[28..32];
    assert dw[4*(10-4)..4*(10-4)+4] == dw[24..28];
    assert dw[4*(10-5)..4*(10-5)+4] == dw[20..24];
    assert dw[4*(10-6)..4*(10-6)+4] == dw[16..20];
    assert dw[4*(10-7)..4*(10-7)+4] == dw[12..16];
    assert dw[4*(10-8)..4*(10-8)+4] == dw[8..12];
    assert dw[4*(10-9)..4*(10-9)+4] == dw[4..8];
    assert dw[4*(10-10)..4*(10-10)+4] == dw[0..4];

    lemma_AES128DecryptRaw(key, input, AES_128(), dw, s,
                           seq_to_Quadword(dw[0..4]),
                           seq_to_Quadword(dw[4..8]),
                           seq_to_Quadword(dw[8..12]),
                           seq_to_Quadword(dw[12..16]),
                           seq_to_Quadword(dw[16..20]),
                           seq_to_Quadword(dw[20..24]),
                           seq_to_Quadword(dw[24..28]),
                           seq_to_Quadword(dw[28..32]),
                           seq_to_Quadword(dw[32..36]),
                           seq_to_Quadword(dw[36..40]),
                           seq_to_Quadword(dw[40..44]),
                           input,
                           trace[0], trace[1], trace[2], trace[3], trace[4], trace[5], trace[6], trace[7], trace[8], trace[9], trace[10]);
}

}
