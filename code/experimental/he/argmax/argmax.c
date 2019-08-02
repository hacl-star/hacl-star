extern "C" {
#include "Hacl_Impl_Bignum.h"
}

#include <iostream>
#include <random>


void argmax_gogo () {
    uint64_t n[2] = { 0, (uint64_t)127U };
    uint64_t a[2] = { 0, (uint64_t)55U };
    uint64_t b[1] = { (uint64_t)100U };
    uint64_t c[2] = { 0, 0 };
    Hacl_Impl_Bignum_Modular_bn_modular_add(2, n, a, b, c);
    std::cout << c[0] << " " << c[1] << std::endl;
}

int main()
{
    argmax_gogo();
    printf ("Benchmarks should be here\n");
    std::cout << "Benchmarks should be here" << std::endl;
    return 0;
}
