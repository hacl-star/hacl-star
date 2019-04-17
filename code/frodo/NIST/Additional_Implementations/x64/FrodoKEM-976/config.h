/********************************************************************************************
* FrodoKEM: Learning with Errors Key Encapsulation
*
* Abstract: configuration file
*********************************************************************************************/

#ifndef _CONFIG_H_
#define _CONFIG_H_


// Definition of operating system

#define OS_LINUX     1

#if defined(LINUX)            // Linux
    #define OS_TARGET OS_LINUX 
#else
    #error -- "Unsupported OS"
#endif


// Definition of compiler

#define COMPILER_GCC     1
#define COMPILER_CLANG   2

#if defined(__GNUC__)           // GNU GCC compiler
    #define COMPILER COMPILER_GCC   
#elif defined(__clang__)        // Clang compiler
    #define COMPILER COMPILER_CLANG
#else
    #error -- "Unsupported COMPILER"
#endif


// Definition of the targeted architecture and basic data types
    
#define TARGET_AMD64        1

#if defined(_AMD64_)
    #define TARGET TARGET_AMD64
#else
    #error -- "Unsupported ARCHITECTURE"
#endif


#if defined(LINUX)
    #define ALIGN_HEADER(N)
    #define ALIGN_FOOTER(N) __attribute__((aligned(N)))
#endif


// Selecting implementation: optimized_fast
#if defined(_OPTIMIZED_FAST_)    // "Optimized_fast" implementation requires support for AVX2 and AES_NI instructions 
    #define USE_AVX2 
    #define AES_ENABLE_NI 
    #define USE_OPTIMIZED_FAST
#else
    #error -- unsupported implementation
#endif


// Defining method for generating matrix A
#if (_AES128_FOR_A_)
    #define USE_AES128_FOR_A
#elif defined(_CSHAKE128_FOR_A_)
    #define USE_CSHAKE128_FOR_A
#else
    ##error -- missing method for generating matrix A
#endif


// Selecting use of OpenSSL's AES functions
#if defined(_USE_OPENSSL_)
    #define USE_OPENSSL
#endif


// Macro to avoid compiler warnings when detecting unreferenced parameters
#define UNREFERENCED_PARAMETER(PAR) ((void)(PAR))


#endif
