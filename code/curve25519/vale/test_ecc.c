#include <stdio.h>
#include <stdint.h>
//#include <chrono>
#include <math.h>
#include <inttypes.h>

typedef unsigned char byte;
double cpuFreq;

extern void mul(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void sqr(const uint64_t* dst, const uint64_t* in_a); 
extern uint64_t mul1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern uint64_t sub1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t sub(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);


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
*/

void init_uint64s(uint64_t* buf, int len) {
  for (int i = 0; i < len; i++) {
    buf[i] = i;
  }
}

#define ALIGN __attribute__((aligned(16))) 
void test() {
    ALIGN uint64_t A[4];
    ALIGN uint64_t B[4];
    ALIGN uint64_t D[8];

    init_uint64s(A, 4);
    init_uint64s(B, 4);

    
    for (int i = 0; i < 10; i++)
    {
//        auto time1 = std::chrono::high_resolution_clock::now();
//        uint64_t start = GetRDTSC();
        int n = 10000;
        for (int j = 0; j < n; j++)
        {
            mul(D, A, B);
            sqr(D, A);
            uint64_t overflow;
            overflow = mul1(D, A, 42);
            overflow = add1(D, A, 330);
            overflow = add (D, A, B);
        }
//        uint64_t end = GetRDTSC();
//        auto time2 = std::chrono::high_resolution_clock::now();
//        int dt = std::chrono::duration_cast<std::chrono::microseconds>(time2 - time1).count();
//        printf("time = %d microseconds for %d iterations (%lf MB/s)\n", dt, n, double(n) * (nblocks * 64) / dt);
//        printf("cycle diff = %llu, time = %fs\n", end - start, (end - start) / cpuFreq);
    }
}

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
    test();

    printf("goodbye\n");
    return 0;
}
