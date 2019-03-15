#ifndef CPUCYCLES_H
#define CPUCYCLES_H
    
#include "../config.h"

#if (TARGET == TARGET_ARM || TARGET == TARGET_ARM64)
    #define print_unit printf("nsec");
#else
    #define print_unit printf("cycles");
#endif

    
// Access system counter for benchmarking
int64_t cpucycles(void);

#endif
