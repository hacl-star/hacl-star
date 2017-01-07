include "aes.s.dfy"

// Derived from RFC 5246 section 6.2.3.2, at https://tools.ietf.org/html/rfc5246#section-6.2.3.2

module CBCModule {

import opened AESModule

function CBC_Encrypt(key:seq<uint32>, input:seq<Quadword>, alg:Algorithm, IV:Quadword) : seq<Quadword>
    requires |key| == Nk(alg);
    requires |input| > 0;
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to Cipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to Cipher
{
    if |input| == 1 then
        [AES_Encrypt(key, QuadwordXor(input[0], IV), alg)]
    else
        var rest := CBC_Encrypt(key, all_but_last(input), alg, IV);
        rest + [AES_Encrypt(key, QuadwordXor(last(input), last(rest)), alg)]
}

function CBC_Decrypt(key:seq<uint32>, input:seq<Quadword>, alg:Algorithm, IV:Quadword) : seq<Quadword>
    requires |key| == Nk(alg);
    requires |input| > 0;
    requires (Nb() * (Nr(alg) + 1)) / 4 == Nr(alg) + 1;   // Easy to prove, but necessary precondition to InvCipher
    requires (Nb() * (Nr(alg) + 1)) % 4 == 0;   // Easy to prove, but necessary precondition to InvCipher
{
    if |input| == 1 then
        [QuadwordXor(AES_Decrypt(key, input[0], alg), IV)]
    else
        var rest := CBC_Decrypt(key, all_but_last(input), alg, IV);
        rest + [QuadwordXor(AES_Decrypt(key, last(input), alg), input[|input|-2])]
}

}
