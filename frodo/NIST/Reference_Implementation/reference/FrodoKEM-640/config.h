/********************************************************************************************
* FrodoKEM: Learning with Errors Key Encapsulation
*
* Abstract: configuration file
*********************************************************************************************/

#ifndef _CONFIG_H_
#define _CONFIG_H_


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
#define TARGET_x86          2
#define TARGET_ARM          3

#if defined(_AMD64_)
    #define TARGET TARGET_AMD64 
#elif defined(_X86_)
    #define TARGET TARGET_x86
#elif defined(_ARM_)
    #define TARGET TARGET_ARM
#else
    #error -- "Unsupported ARCHITECTURE"
#endif


// Selecting implementation: reference implementation
#if defined(_REFERENCE_)
    #define USE_REFERENCE
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
