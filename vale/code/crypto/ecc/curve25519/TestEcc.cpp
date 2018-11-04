#include <stdio.h>
#include <stdint.h>
#include <chrono>
#include <math.h>
#include <inttypes.h>

typedef unsigned char byte;
double cpuFreq;

extern "C" void mul(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern "C" void sqr(const uint64_t* dst, const uint64_t* in_a);
extern "C" uint64_t mul1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern "C" uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern "C" uint64_t add(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);


/*
#ifdef _WIN32
#include <intrin.h>
#include <Windows.h>
#pragma intrinsic(__rdtsc)
#else
#include <unistd.h> // For sleep() 
#define Sleep(x) usleep(x*1000)
#endif

void printbytes(char *label, byte *b, int len)
{
    printf("%s:", label);
    for (int i = 0; i < len; i++) printf(" %2x", unsigned(b[i]));
    printf("\n");
}

uint64_t GetRDTSC() {
        //VS on x64 doesn't support inline assembly
   //__asm {
   //   ; Flush the pipeline
   //   XOR eax, eax
   //   CPUID
   //   ; Get RDTSC counter in edx:eax
   //   RDTSC
   //}
#ifdef _WIN32
        int CPUInfo[4];
        int InfoType = 0;
   __cpuid(CPUInfo, InfoType); // Serialize the pipeline
   return (unsigned __int64)__rdtsc();
#else
//        uint64_t rv;
//        __asm__ (
//                "push           %%rbx;"
//                "cpuid;"
//                "pop            %%rbx;"
//                :::"%rax","%rcx","%rdx");
//        __asm__ __volatile__ ("rdtsc" : "=A" (rv));
//        return (rv);
        unsigned int tickl, tickh;
        __asm__ __volatile__("rdtsc":"=a"(tickl),"=d"(tickh));
        return ((unsigned long long)tickh << 32)|tickl;
#endif // _WIN32
}


void print_ints(int size, unsigned int ints[]) {
	int i;
	for (i = 0; i < size; i++) {
		printf("%08x ", ints[i]);
	}
}

void test() {
    unsigned int K[64];
    init_k(K);

    unsigned int hash[8];
    init_hash(hash);

//    printf("The sha256 output for '' is: \n\t");
//    print_ints(8, hash);
//    printf("\nExpected answer is:\n\te3b0c442 98fc1c14 9afbf4c8 996fb924 27ae41e4 649b934c a495991b 7852b855\n");

    int nblocks = 256;
    byte *in = new byte[nblocks * 64+128];

    // Make sure the buffers are 128-bit aligned
    int byte_offset = 128 - (((unsigned long long) in) % 128);
    in = (byte*) (((unsigned long long) in) + byte_offset); 
    for (int i = 0; i < nblocks * 64; i++)
    {
        in[i] = i % 256;
    }
    for (int i = 0; i < 10; i++)
    {
        auto time1 = std::chrono::high_resolution_clock::now();
        uint64_t start = GetRDTSC();
        int n = 10000;
        for (int j = 0; j < n; j++)
        {
            sha256((byte*)hash, in, nblocks, (byte*)K);

        }
        uint64_t end = GetRDTSC();
        auto time2 = std::chrono::high_resolution_clock::now();
        int dt = std::chrono::duration_cast<std::chrono::microseconds>(time2 - time1).count();
        printf("time = %d microseconds for %d iterations (%lf MB/s)\n", dt, n, double(n) * (nblocks * 64) / dt);
        printf("cycle diff = %llu, time = %fs\n", end - start, (end - start) / cpuFreq);
    }
}
*/

int main()
{
    printf("hello\n");

//    // Calibrate frequency
//    uint64_t startTime = GetRDTSC();
//    Sleep(200);  // Sleep for 200ms
//    uint64_t stopTime = GetRDTSC();
//
//    cpuFreq = (stopTime - startTime) / (200 / 1000.0);
//
//    printf("Measured CPU at %f GHz\n", cpuFreq/pow(10.0, 9));
//
//    test();


    printf("goodbye\n");
    return 0;
}
