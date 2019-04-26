
#ifdef _MSC_VER

#include <Windows.h>

typedef LONGLONG TIME;

void get_time(TIME *t)
{
    LARGE_INTEGER offset;
    QueryPerformanceCounter( &offset );
    *t = offset.QuadPart;
}

double time_diff_in_secs(TIME *before, TIME *after)
{
    LARGE_INTEGER hfreq;
    QueryPerformanceFrequency( &hfreq );
    return ( ( *after - *before ) / (double) hfreq.QuadPart );
}


#else

#include <time.h>

typedef struct timespec TIME;

void get_time(TIME *t)
{
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, t);
}

double time_diff_in_secs(TIME *from, TIME *to)
{
    return ((to->tv_sec - from->tv_sec) * 1e9l + (to->tv_nsec - from->tv_nsec)) / 1000000000.0;
}

#endif


#include "ed25519-c/Hacl_Ed25519.h"

int main(void)
{
    TIME before, after;
    unsigned char private_key[32];
    unsigned char keys[96];
    unsigned char *public_key = keys; /* (leading 32 bytes) */

    srand((unsigned)time(NULL));

    for (int i=0; i < 32; i++)
        private_key[i] = rand() % 128;

    Hacl_Ed25519_expand_keys( keys, private_key );

    printf( "len [b] | t_sig [s] |    sig/s | t_ver [s] |    ver/s\n" );
    printf( "-----------------------------------------------------\n" );

    for (int sz = 32; sz <= 65536; sz *= 2)
    {
        unsigned char *msg = malloc( sz );
        unsigned char signature[64];
        unsigned its = 1000;

        for (int i=0; i < sz; i++)
            msg[i] = rand() % 128;

        get_time(&before);
        for (unsigned i = its; i > 0; i--)
            Hacl_Ed25519_sign_expanded(signature, keys, sz, msg);
        get_time(&after);
        double sign_time = time_diff_in_secs(&before, &after);

        get_time(&before);
        for (unsigned i = its; i > 0; i--)
        {
            bool r = Hacl_Ed25519_verify(public_key, sz, msg, signature);
            if (!r) printf("Signature verification failed!\n");
        }
        get_time(&after);
        double verify_time = time_diff_in_secs(&before, &after);

        printf("% 7d | % 9.2f | %8.2f | % 9.2f | %8.2f\n", sz, sign_time, its/sign_time, verify_time, its/verify_time );

        free( msg );
   }

    return 0;
}
