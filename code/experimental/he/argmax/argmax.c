#include "Hacl_Impl_Bignum_Misc.h"
#include "Hacl_Impl_Bignum_Modular.h"
#include "Hacl_Impl_HE_Paillier.h"
#include "Hacl_Impl_Bignum_Comparison.h"
#include "Hacl_Impl_HE_GM.h"

#include <iostream>
#include <random>


void test_paillier () {
    uint64_t a[1U] = { (uint64_t)128U };
    uint64_t b[1U] = { (uint64_t)55U };
    uint64_t* c = { 0, 0 };
    std::cout << res0[0] << std::endl;
}

int main()
{
    test_paillier();
    std::cout << "Benchmarks should be here" << std::endl;
    return 0;
}
