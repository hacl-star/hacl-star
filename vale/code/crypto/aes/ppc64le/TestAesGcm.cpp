#include <time.h> 
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "aes-gcm.h"

typedef unsigned char byte;

const byte key[16] = { 0xE8, 0xE9, 0xEA, 0xEB, 0xED, 0xEE, 0xEF, 0xF0, 0xF2, 0xF3, 0xF4, 0xF5, 0xF7, 0xF8, 0xF9, 0xFA };
byte iv[16] =
    { 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 0, 0, 0, 0 };

void test() {
    byte expanded_aes_key[16*11];
    byte expanded_h_key[16*3];
    byte tag[16];
    
    int nblocks = 7;
    int leftovers = 9;
    byte *in = new byte[nblocks*16+leftovers];
    byte *out = new byte[nblocks*16+leftovers];
    for (int i = 0; i < (nblocks*16+leftovers); i++)
    {
        in[i] = i;
    }
    byte final_block[16];
    memcpy(final_block, in + nblocks*16, leftovers);

    int auth_nblocks = 3;
    int auth_leftovers = 7;
    byte *auth_in = new byte[auth_nblocks*16+auth_leftovers];
    for (int i = 0; i < (auth_nblocks*16+auth_leftovers); i++)
    {
        auth_in[i] = i;
    }
    byte auth_final_block[16];
    memcpy(auth_final_block, auth_in + auth_nblocks*16, auth_leftovers);

    aes128_key_expansion(expanded_aes_key, key);
    aes128_keyhash_init(expanded_h_key, expanded_aes_key);

    gcm_args args;
    args.auth_final_block = auth_final_block;
    args.plaintext = in;
    args.ciphertext = out;
    args.plain_block_num = nblocks;
    args.text_final_block = final_block;
    args.plain_len = nblocks*16+leftovers;
    args.additional_data = auth_in;
    args.auth_block_num = auth_nblocks;
    args.additional_data_len = auth_nblocks*16+auth_leftovers;
    args.iv = iv;
    args.expanded_key = expanded_aes_key;
    args.expanded_h_key = expanded_h_key;
    args.tag = tag;

    clock_t t;
    double time_taken;
    t = clock(); 
    for (uint32_t i = 0; i < 100; i++)
        gcm128_encrypt(&args);
    t = clock() - t; 
    time_taken = ((double)t)/CLOCKS_PER_SEC; 
    printf("time elapsed %f seconds\n", time_taken/100);

    memcpy(out + nblocks*16, final_block, leftovers);
}

int main()
{
    test();

    printf("goodbye\n");
    return 0;
}
