#include <time.h> 
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef unsigned char byte;

extern "C" void sha256_update(byte* ctx, byte* input, int num_blocks, byte* k);

void init_hash(unsigned int hash[8]) {
    hash[0] = 0x6a09e667;
    hash[1] = 0xbb67ae85;
    hash[2] = 0x3c6ef372;
    hash[3] = 0xa54ff53a;
    hash[4] = 0x510e527f;
    hash[5] = 0x9b05688c;
    hash[6] = 0x1f83d9ab;
    hash[7] = 0x5be0cd19;
}

void init_k(unsigned int K[64]) {
  int i = 0;
    K[i++] = 0x428a2f98;
    K[i++] = 0x71374491;
    K[i++] = 0xb5c0fbcf;
    K[i++] = 0xe9b5dba5;
    K[i++] = 0x3956c25b;
    K[i++] = 0x59f111f1;
    K[i++] = 0x923f82a4;
    K[i++] = 0xab1c5ed5;

    K[i++] = 0xd807aa98;
    K[i++] = 0x12835b01;
    K[i++] = 0x243185be;
    K[i++] = 0x550c7dc3;
    K[i++] = 0x72be5d74;
    K[i++] = 0x80deb1fe;
    K[i++] = 0x9bdc06a7;
    K[i++] = 0xc19bf174;

    K[i++] = 0xe49b69c1;
    K[i++] = 0xefbe4786;
    K[i++] = 0x0fc19dc6;
    K[i++] = 0x240ca1cc;
    K[i++] = 0x2de92c6f;
    K[i++] = 0x4a7484aa;
    K[i++] = 0x5cb0a9dc;
    K[i++] = 0x76f988da;

    K[i++] = 0x983e5152;
    K[i++] = 0xa831c66d;
    K[i++] = 0xb00327c8;
    K[i++] = 0xbf597fc7;
    K[i++] = 0xc6e00bf3;
    K[i++] = 0xd5a79147;
    K[i++] = 0x06ca6351;
    K[i++] = 0x14292967;

    K[i++] = 0x27b70a85;
    K[i++] = 0x2e1b2138;
    K[i++] = 0x4d2c6dfc;
    K[i++] = 0x53380d13;
    K[i++] = 0x650a7354;
    K[i++] = 0x766a0abb;
    K[i++] = 0x81c2c92e;
    K[i++] = 0x92722c85;

    K[i++] = 0xa2bfe8a1;
    K[i++] = 0xa81a664b;
    K[i++] = 0xc24b8b70;
    K[i++] = 0xc76c51a3;
    K[i++] = 0xd192e819;
    K[i++] = 0xd6990624;
    K[i++] = 0xf40e3585;
    K[i++] = 0x106aa070;

    K[i++] = 0x19a4c116;
    K[i++] = 0x1e376c08;
    K[i++] = 0x2748774c;
    K[i++] = 0x34b0bcb5;
    K[i++] = 0x391c0cb3;
    K[i++] = 0x4ed8aa4a;
    K[i++] = 0x5b9cca4f;
    K[i++] = 0x682e6ff3;

    K[i++] = 0x748f82ee;
    K[i++] = 0x78a5636f;
    K[i++] = 0x84c87814;
    K[i++] = 0x8cc70208;
    K[i++] = 0x90befffa;
    K[i++] = 0xa4506ceb;
    K[i++] = 0xbef9a3f7;
    K[i++] = 0xc67178f2;
}

void test() {
    unsigned int K[64];
    init_k(K);

    unsigned int hash[8];
    init_hash(hash);

    int nblocks = 256;
    byte *in = new byte[nblocks * 64+128];

    // Make sure the buffers are 128-bit aligned
    int byte_offset = 128 - (((unsigned long long) in) % 128);
    in = (byte*) (((unsigned long long) in) + byte_offset); 
    for (int i = 0; i < nblocks * 64; i++)
    {
        in[i] = i % 256;
    }
    clock_t t;
    double time_taken;
    t = clock(); 
    for (uint32_t i = 0; i < 100; i++)
        sha256_update((byte*)hash, in, nblocks, (byte*)K);
    t = clock() - t; 
    time_taken = ((double)t)/CLOCKS_PER_SEC; 
    printf("time elapsed %f seconds\n", time_taken/100);
}

int main()
{
    test();

    printf("goodbye\n");
    return 0;
}
