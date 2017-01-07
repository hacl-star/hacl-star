include "../../lib/util/operations.s.dfy"
include "../../lib/util/words_and_bytes.s.dfy"
include "../../lib/collections/Seqs.s.dfy"

module AESModule {

import opened operations_s
import opened words_and_bytes_s
import opened Collections__Seqs_s

// AES specification based on FIPS-197
// Intel instructions based on Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 2

//////////////////////////////////////////////////////////////////////////
//
//  AES constants
//
//////////////////////////////////////////////////////////////////////////

function AES_Rcon() : seq<uint32>
{
    [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]
}

datatype Algorithm = AES_128 | AES_192 | AES_256

// AES fixes Rijndael's block size at 4 32-bit words
function Nb() : int { 4 }

// Number of key words
function Nk(alg:Algorithm) : int
{
    match alg
        case AES_128 => 4
        case AES_192 => 6
        case AES_256 => 8
}

// Number of rounds
function Nr(alg:Algorithm) : int
{
    match alg
        case AES_128 => 10
        case AES_192 => 12
        case AES_256 => 14
}

//////////////////////////////////////////////////////////////////////////
//
//  AES specification low-level routines
//
//////////////////////////////////////////////////////////////////////////

function GetSBox() : seq<seq<uint8>>
    ensures |GetSBox()| == 16;
    ensures forall i :: 0 <= i < 16 ==> |GetSBox()[i]| == 16;
{
    [[0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76],
     [0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0],
     [0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15],
     [0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75],
     [0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84],
     [0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf],
     [0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8],
     [0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2],
     [0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73],
     [0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb],
     [0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79],
     [0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08],
     [0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a],
     [0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e],
     [0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf],
     [0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]]
}

function GetInvSBox() : seq<seq<uint8>>
    ensures |GetInvSBox()| == 16;
    ensures forall i :: 0 <= i < 16 ==> |GetInvSBox()[i]| == 16;
{
    [[0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb],
     [0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb],
     [0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e],
     [0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25],
     [0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92],
     [0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84],
     [0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06],
     [0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b],
     [0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73],
     [0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e],
     [0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b],
     [0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4],
     [0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f],
     [0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef],
     [0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61],
     [0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d]]
}

function ApplyBox(b:uint8, box:seq<seq<uint8>>) : uint8
    requires |box| == 16;
    requires forall i :: 0 <= i < 16 ==> |box[i]| == 16;
{
    box[b/16][b%16]
}

function SubWordUsingBox(w:uint32, box:seq<seq<uint8>>) : uint32
    requires |box| == 16;
    requires forall i :: 0 <= i < 16 ==> |box[i]| == 16;
{
    var bytes := WordToBytes(w);
    BytesToWord(ApplyBox(bytes[0], box), ApplyBox(bytes[1], box), ApplyBox(bytes[2], box), ApplyBox(bytes[3], box))
}

function SubWord(w:uint32) : uint32
{
    SubWordUsingBox(w, GetSBox())
}

function InvSubWord(w:uint32) : uint32
{
    SubWordUsingBox(w, GetInvSBox())
}

function SubBytes(s:Quadword) : Quadword
{
    Quadword(SubWord(s.lo), SubWord(s.mid_lo), SubWord(s.mid_hi), SubWord(s.hi))
}

function {:axiom} ShiftRows(s:Quadword) : Quadword

function {:axiom} MixColumns(s:Quadword) : Quadword

function InvSubBytes(s:Quadword) : Quadword
{
    Quadword(InvSubWord(s.lo), InvSubWord(s.mid_lo), InvSubWord(s.mid_hi), InvSubWord(s.hi))
}

function {:axiom} InvShiftRows(s:Quadword) : Quadword

function method {:axiom} InvMixColumns(s:Quadword) : Quadword

function AddRoundKey(s:Quadword, rk:Quadword) : Quadword
{
    QuadwordXor(s, rk)
}

function Quadword_to_seq(qw:Quadword) : seq<uint32>
    ensures |Quadword_to_seq(qw)| == 4;
{
    [qw.lo, qw.mid_lo, qw.mid_hi, qw.hi]
}

function seq_to_Quadword(s:seq<uint32>) : Quadword
    requires |s| == 4;
{
    Quadword(s[0], s[1], s[2], s[3])
}

//////////////////////////////////////////////////////////////////////////
//
//  AES specification high-level operations
//
//////////////////////////////////////////////////////////////////////////

function Round(inp:Quadword, round_key:Quadword) : Quadword
{
    var qw1 := SubBytes(inp);
    var qw2 := ShiftRows(qw1);
    var qw3 := MixColumns(qw2);
    var qw4 := AddRoundKey(qw3, round_key);
    qw4
}

function Rounds(inp:Quadword, round_keys:seq<Quadword>) : Quadword
    decreases |round_keys|;
{
    if round_keys == [] then inp
    else Rounds(Round(inp, round_keys[0]), round_keys[1..])
}
 
// NB: The index notation for the key schedule (w) is rather confusing.
//     What it's attempting to convey (I believe) is that w consists of
//     NumRounds+1 (Nr+1) chunks (or round keys), where each chunk is Nb (4) words
//     The notation w[x, y] says use the 4 words starting at x up to y
function Cipher(input:Quadword, round_keys:seq<Quadword>, alg:Algorithm) : Quadword
    requires |round_keys| == Nr(alg) + 1;
{
    var qw1 := input;
    var qw2 := AddRoundKey(qw1, round_keys[0]);
    var qw3 := Rounds(qw2, round_keys[1..Nr(alg)]);
    var qw4 := SubBytes(qw3);
    var qw5 := ShiftRows(qw4);
    var qw6 := AddRoundKey(qw5, round_keys[Nr(alg)]);
    qw6
}

function InvRound(inp:Quadword, inv_round_key:Quadword) : Quadword
{
    var qw1 := inp;
    var qw2 := InvShiftRows(qw1);
    var qw3 := InvSubBytes(qw2);
    var qw4 := AddRoundKey(qw3, inv_round_key);
    var qw5 := InvMixColumns(qw4);
    qw5
}

function InvRounds(inp:Quadword, inv_round_keys:seq<Quadword>) : Quadword
    decreases |inv_round_keys|
{
    if inv_round_keys == [] then inp
    else InvRounds(InvRound(inp, last(inv_round_keys)), all_but_last(inv_round_keys))
}

// See caveats for Cipher
function InvCipher(input:Quadword, inv_round_keys:seq<Quadword>, alg:Algorithm) : Quadword
    requires |inv_round_keys| == Nr(alg) + 1;
{
    var qw1 := input;
    var qw2 := AddRoundKey(qw1, inv_round_keys[Nr(alg)]);
    var qw3 := InvRounds(qw2, inv_round_keys[1..Nr(alg)]);
    var qw4 := InvShiftRows(qw3);
    var qw5 := InvSubBytes(qw4);
    var qw6 := AddRoundKey(qw5, inv_round_keys[0]);
    qw6
}


function EqInvRound(inp:Quadword, inv_round_key:Quadword) : Quadword
{
    var qw1 := inp;
    var qw2 := InvSubBytes(qw1);
    var qw3 := InvShiftRows(qw2);
    var qw4 := InvMixColumns(qw3);
    var qw5 := AddRoundKey(qw4, inv_round_key);
    qw5
}

function EqInvRounds(inp:Quadword, inv_round_keys:seq<Quadword>) : Quadword
    decreases |inv_round_keys|
{
    if inv_round_keys == [] then inp
    else EqInvRounds(EqInvRound(inp, last(inv_round_keys)), all_but_last(inv_round_keys))
}

function EqInvCipher(input:Quadword, inv_round_keys:seq<Quadword>, alg:Algorithm) : Quadword
    requires |inv_round_keys| == Nr(alg) + 1;
{
    var qw1 := input;
    var qw2 := AddRoundKey(qw1, inv_round_keys[Nr(alg)]);
    var qw3 := EqInvRounds(qw2, inv_round_keys[1..Nr(alg)]);
    var qw4 := InvSubBytes(qw3);
    var qw5 := InvShiftRows(qw4);
    var qw6 := AddRoundKey(qw5, inv_round_keys[0]);
    qw6
}

function RotWord(x:uint32) : uint32
{
    var bytes := WordToBytes(x);
    BytesToWord(bytes[1], bytes[2], bytes[3], bytes[0])
}

function KeyScheduleWordsToRoundKeysPartial(w:seq<uint32>, rounds:int) : seq<Quadword>
    requires 0 <= rounds;
    requires |w| >= 4 * rounds;
    ensures  |KeyScheduleWordsToRoundKeysPartial(w, rounds)| == rounds;
    ensures  forall i :: 0 <= i < rounds ==> var rk := KeyScheduleWordsToRoundKeysPartial(w, rounds)[i];
                                      rk == Quadword(w[4*i], w[4*i+1], w[4*i+2], w[4*i+3]);
{
    if rounds == 0 then
        []
    else
        var round_keys := KeyScheduleWordsToRoundKeysPartial(w, rounds - 1);
        var rk:Quadword := Quadword(w[4 * rounds - 4], w[4 * rounds - 3], w[4 * rounds - 2], w[4 * rounds - 1]);
        round_keys + [rk]
}

function KeyScheduleWordsToRoundKeys(w:seq<uint32>) : seq<Quadword>
    requires |w| % 4 == 0;
    ensures  |KeyScheduleWordsToRoundKeys(w)| == |w| / 4;
    //ensures  var keys := KeyScheduleWordsToRoundKeys(w);
    //         forall i :: 0 <= i < |keys| ==> valid_round_key(keys[i]);
    ensures  var keys := KeyScheduleWordsToRoundKeys(w);
             forall i :: 0 <= i < |keys| ==> keys[i] == Quadword(w[4*i], w[4*i+1], w[4*i+2], w[4*i+3]);
{
    KeyScheduleWordsToRoundKeysPartial(w, |w| / 4)
}
 
function ExpandKeyPartial(key:seq<uint32>, alg:Algorithm, sz:int) : seq<uint32>
    requires |key| == Nk(alg);
    requires 0 <= sz <= Nb() * (Nr(alg) + 1);
    ensures  |ExpandKeyPartial(key, alg, sz)| == sz;
{
    if sz == 0 then
        []
    else
        var w := ExpandKeyPartial(key, alg, sz - 1);
        var i := sz - 1;
        if 0 <= i < Nk(alg) then
            w + [key[i]]
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
            w + [BitwiseXor(w[i - Nk(alg)], temp)]
}

function ExpandKey(key:seq<uint32>, alg:Algorithm) : seq<uint32>
    requires |key| == Nk(alg);
{
    if Nb() * (Nr(alg) + 1) >= 0 then ExpandKeyPartial(key, alg, Nb() * (Nr(alg) + 1)) else []
}

function EqInvExpandKeyPartial(key:seq<uint32>, alg:Algorithm, round:int) : seq<uint32>
    requires |key| == Nk(alg);
    requires 0 <= round <= Nr(alg);
    ensures  |EqInvExpandKeyPartial(key, alg, round)| == (round+1) * 4;
{
    var w := ExpandKey(key, alg);
    var keywords := if 0 <= Nb() * round <= Nb() * (round + 1) <= |w| then w[Nb() * round .. Nb() * (round + 1)] else [0, 0, 0, 0];
    if round == 0 then
        keywords
    else if round < Nr(alg) then
        EqInvExpandKeyPartial(key, alg, round - 1) + Quadword_to_seq(InvMixColumns(Quadword(keywords[0], keywords[1], keywords[2], keywords[3])))
    else
        EqInvExpandKeyPartial(key, alg, round - 1) + keywords
}

function EqInvExpandKey(key:seq<uint32>, alg:Algorithm) : seq<uint32>
    requires |key| == Nk(alg);
{
    EqInvExpandKeyPartial(key, alg, Nr(alg))
}

function AES_Encrypt(key:seq<uint32>, input:Quadword, alg:Algorithm) : Quadword
    requires |key| == Nk(alg);
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to Cipher
{
    Cipher(input, KeyScheduleWordsToRoundKeys(ExpandKey(key, alg)), alg)
}

function AES_Decrypt(key:seq<uint32>, input:Quadword, alg:Algorithm) : Quadword
    requires |key| == Nk(alg);
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to Cipher
{
    InvCipher(input, KeyScheduleWordsToRoundKeys(ExpandKey(key, alg)), alg)
}

function AES_EquivDecrypt(key:seq<uint32>, input:Quadword, alg:Algorithm) : Quadword
    requires |key| == Nk(alg);
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to Cipher
{
    EqInvCipher(input, KeyScheduleWordsToRoundKeys(EqInvExpandKey(key, alg)), alg)
}


//////////////////////////////////////////////////////////////////////////
//
//  Axiomatized properties from the FIPS spec
//
//////////////////////////////////////////////////////////////////////////

// Property 1 in 5.3.5
lemma {:axiom} SubBytes_ShiftRows_commute()
    ensures forall s :: SubBytes(ShiftRows(s)) == ShiftRows(SubBytes(s));
    ensures forall s :: InvSubBytes(InvShiftRows(s)) == InvShiftRows(InvSubBytes(s));

// Property 2 in 5.3.5
lemma {:axiom} MixColumns_linearity()
    ensures forall s, round_key :: InvMixColumns(QuadwordXor(s, round_key)) == QuadwordXor(InvMixColumns(s), InvMixColumns(round_key));

// non-trigger-y version of lemmas above
lemma {:axiom} SubBytesShiftRowsCommutativity(s:Quadword)
    ensures SubBytes(ShiftRows(s)) == ShiftRows(SubBytes(s));

lemma {:axiom} InvSubBytesInvShiftRowsCommutativity(s:Quadword)
    ensures InvSubBytes(InvShiftRows(s)) == InvShiftRows(InvSubBytes(s));

lemma {:axiom} MixColumns_linearity_specific(s:Quadword, round_key:Quadword)
    ensures InvMixColumns(QuadwordXor(s, round_key)) == QuadwordXor(InvMixColumns(s), InvMixColumns(round_key));

// TODO: Use the axioms above to prove:
/*
lemma InvCiphersEquiv(key:seq<uint32>, input:uint32seq, alg:Algorithm) : uint32seq
    requires |key| == Nk(alg);
    requires valid_uint32seq(input);
    requires exists w :: |w| == Nb() * (Nr(alg) + 1) && KeyExpansionPredicate(key, alg, w);
    ensures  InvCipher(input, w, alg) == EqInvCipher(input, ModifiedRoundKey(w), alg);
*/

//////////////////////////////////////////////////////////////////////////
//
//  XMM instructions
//
//////////////////////////////////////////////////////////////////////////

function select_word(xmm:Quadword, selector:twobits) : uint32
{
    if selector == 0 then xmm.lo
    else if selector == 1 then xmm.mid_lo
    else if selector == 2 then xmm.mid_hi
    else if selector == 3 then xmm.hi
    else
        42 
}

}
