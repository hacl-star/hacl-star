include "../sha256.s.dfy"
include "../../../lib/util/operations.i.dfy"

module bit_vector_lemmas_i {

import opened sha256_s
import opened operations_i

lemma  lemma_Maj(x:uint32, y:uint32, z:uint32, result:uint32)
    requires result == BitwiseXor(BitwiseAnd(BitwiseXor(y, z), BitwiseXor(x, y)), y);
    ensures  result == Maj(x, y, z);
{
    reveal_Maj();
    reveal_BitXor();
    reveal_BitAnd();
    lemma_BitsAndWordConversions();
}

lemma lemma_Ch(x:uint32, y:uint32, z:uint32, result:uint32)
    requires result == BitwiseXor(BitwiseAnd(BitwiseXor(y, z), x), z);
    ensures  result == Ch(x, y, z);
{
    reveal_Ch();
    reveal_BitNot();
    reveal_BitXor();
    reveal_BitAnd();
    lemma_BitsAndWordConversions();
}

}
