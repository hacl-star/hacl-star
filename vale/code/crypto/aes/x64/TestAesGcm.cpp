#include <stdio.h>
#include <stdint.h>
#include <chrono>

#ifdef LOWSTAR
#include "Low_GCMencrypt.h"
#endif // LOWSTAR

typedef unsigned char byte;

struct args
{
    byte *plain_ptr;
    uint64_t plain_num_bytes;
    byte *auth_ptr;
    uint64_t auth_num_bytes;
    byte *iv_ptr;
    byte *expanded_key_ptr;
    byte *out_ptr;
    byte *tag_ptr;
};

extern "C" void aes128_key_expansion(byte *key_ptr, byte *key_expansion_ptr);
extern "C" void gcm128_encrypt(args *a);
extern "C" int gcm128_decrypt(args *a);

extern "C" void aes256_key_expansion(byte *key_ptr, byte *key_expansion_ptr);
extern "C" void gcm256_encrypt(args *a);
extern "C" int gcm256_decrypt(args *a);


byte key[32] =
    { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
     16,17,18,19,20,21,22,23,24,25, 26, 27, 28, 29, 30, 31 };
byte key_expansion[15 * (128/8)];

byte plain[32] =
    { 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215,
      216, 217, 218, 99,  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0
    };
byte auth[1]; // actually size 0
byte iv[16] =
    { 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 0, 0, 0, 0 };
byte out[32];
byte tag[16];

void printbytes(char *label, byte *b, int len)
{
    printf("%s:", label);
    for (int i = 0; i < len; i++) printf(" %2x", unsigned(b[i]));
    printf("\n");
}

void test(void (*aes_key_expansion) (byte*, byte*),
          void (*gcm_encrypt) (args*),
          int  (*gcm_decrypt) (args*),
          int num_rounds)
{
    args a;
    a.plain_ptr = plain;
    a.plain_num_bytes = 19;
    a.auth_ptr = auth;
    a.auth_num_bytes = 0;
    a.iv_ptr = iv;
    a.expanded_key_ptr = key_expansion;
    a.out_ptr = out;
    a.tag_ptr = tag;
    printbytes((char*)"original plaintext", plain, 19);
    printbytes((char*)"key", key, 16);
    aes_key_expansion(key, key_expansion);
    printbytes((char*)"key_expansion", key_expansion, (num_rounds + 1) * 16);
    gcm_encrypt(&a);
    printbytes((char*)"cipher", out, 19);
    printbytes((char*)"tag", tag, 16);

    a.out_ptr = plain;
    a.plain_ptr = out;
    int ret = gcm_decrypt(&a);
    printf("gcm_decrypt returned %d\n", ret);
    printbytes((char*)"plaintext", plain, 19);

    int nblocks = 256;
    byte *plain2 = new byte[nblocks * 16];
    byte *out2 = new byte[nblocks * 16];
    for (int i = 0; i < nblocks * 16; i++)
    {
        plain2[i] = i % 256;
    }
    a.plain_ptr = plain2;
    a.plain_num_bytes = nblocks * 16;
    a.out_ptr = out2;
    for (int i = 0; i < 10; i++)
    {
        auto time1 = std::chrono::high_resolution_clock::now();
        int n = 10000;
        for (int j = 0; j < n; j++)
        {
            gcm_encrypt(&a);
        }
        auto time2 = std::chrono::high_resolution_clock::now();
        int dt = std::chrono::duration_cast<std::chrono::microseconds>(time2 - time1).count();
        printf("time = %d microseconds for %d iterations (%lf MB/s)\n", dt, n, double(n) * (nblocks * 16) / dt);
    }
    printbytes((char*)"cipher", out2, 16);
    printbytes((char*)"tag", tag, 16);
}

#ifdef LOWSTAR

void test_lowstar() {
    byte iv_backup[16];

    // Save a copy of iv, since Low* version modifies it
    memcpy(iv_backup, iv, 16);

    int auth_num_bytes = 0;
    int plain_num_bytes = 19;
    int num_rounds = 10;
    args a;
    a.plain_ptr = plain;
    a.plain_num_bytes = plain_num_bytes;
    a.auth_ptr = auth;
    a.auth_num_bytes = auth_num_bytes;
    a.iv_ptr = iv;
    a.expanded_key_ptr = key_expansion;
    a.out_ptr = out;
    a.tag_ptr = tag;
    printbytes((char*)"original plaintext", plain, 19);
    printbytes((char*)"key", key, 16);
    aes128_key_expansion(key, key_expansion);
    printbytes((char*)"key_expansion", key_expansion, (num_rounds + 1) * 16);

    // Encrypt using Low* version
    Low_GCMencrypt_gcm_core(plain, plain_num_bytes, auth, auth_num_bytes, iv, key_expansion, out, tag);
    //gcm_encrypt(&a);

    printbytes((char*)"cipher", out, 19);
    printbytes((char*)"tag", tag, 16);

    // Restore iv
    memcpy(iv, iv_backup, 16);
    a.out_ptr = plain;
    a.plain_ptr = out;

    // Decrypt using Vale version
    int ret = gcm128_decrypt(&a);
    printf("gcm_decrypt returned %d\n", ret);
    printbytes((char*)"decrypted plaintext", plain, 19);

    int nblocks = 256;
    byte *plain2 = new byte[nblocks * 16];
    byte *out2 = new byte[nblocks * 16];
    for (int i = 0; i < nblocks * 16; i++)
    {
        plain2[i] = i % 256;
    }

    for (int i = 0; i < 10; i++)
    {
        auto time1 = std::chrono::high_resolution_clock::now();
        int n = 10000;
        for (int j = 0; j < n; j++)
        {
          Low_GCMencrypt_gcm_core(plain2, nblocks * 16, auth, auth_num_bytes, iv, key_expansion, out2, tag);
        }
        auto time2 = std::chrono::high_resolution_clock::now();
        int dt = std::chrono::duration_cast<std::chrono::microseconds>(time2 - time1).count();
        printf("time = %d microseconds for %d iterations (%lf MB/s)\n", dt, n, double(n) * (nblocks * 16) / dt);
    }
    printbytes((char*)"cipher", out2, 16);
    printbytes((char*)"tag", tag, 16);
}

#endif // LOWSTAR


int main()
{
    printf("hello\n");

#ifdef LOWSTAR
    test_lowstar();
#else // !LOWSTAR
    printf("\nBeginning 128-bit test...\n");
    test(aes128_key_expansion,
         gcm128_encrypt,
         gcm128_decrypt,
         10);

    printf("\nBeginning 256-bit test...\n");
    test(aes256_key_expansion,
         gcm256_encrypt,
         gcm256_decrypt,
         14);
#endif // LOWSTAR

    printf("goodbye\n");
    return 0;
}
