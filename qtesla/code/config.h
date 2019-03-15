/*************************************************************************************
* qTESLA: an efficient post-quantum signature scheme based on the R-LWE problem
*
* Abstract: configuration file for the reference test code
**************************************************************************************/  

#ifndef __CONFIG_H__
#define __CONFIG_H__

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>


// Definition of operating system

#define OS_WIN       1
#define OS_LINUX     2

#if defined(__WINDOWS__) || defined(__MINGW32__)       // Microsoft Windows OS
    #define OS_TARGET OS_WIN
#elif defined(__LINUX__)                               // Linux OS
    #define OS_TARGET OS_LINUX 
#else
    #error -- "Unsupported OS"
#endif

// On Linux or on Windows building under Cygwin with regular gcc, use %llu for 64-bit unsigned ints,
// because that uses Cygwin's printf/scanf. On Windows building under mingw, use %I64u, because that uses MSVCRT's.
#if defined(__MINGW32__)
    #define USE_PRINTF_I64
#elif defined(__WINDOWS__) && !defined(__CYGWIN__)
    #define USE_PRINTF_I64
#else
    #undef USE_PRINTF_I64
#endif

// Definition of compiler

#define COMPILER_VC      1
#define COMPILER_GCC     2
#define COMPILER_CLANG   3

#if defined(_MSC_VER)           // Microsoft Visual C compiler
    #define COMPILER COMPILER_VC
#elif defined(__GNUC__)         // GNU GCC compiler
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
#define TARGET_ARM64        4

#if defined(_AMD64_)
    #define TARGET TARGET_AMD64
#elif defined(_X86_)
    #define TARGET TARGET_x86
#elif defined(_ARM_)
    #define TARGET TARGET_ARM
#elif defined(_ARM64_)
    #define TARGET TARGET_ARM64
#else
    #error -- "Unsupported ARCHITECTURE"
#endif

#if defined(_PLATFORM_64_)
    #define RADIX           64
    #define RADIX32         32
    typedef uint64_t        digit_t;        // Unsigned 64-bit digit
    typedef int64_t         sdigit_t;       // Signed 64-bit digit
#elif defined(_PLATFORM_32_)
    #define RADIX           32
    #define RADIX32         32
    typedef uint32_t        digit_t;        // Unsigned 32-bit digit
    typedef int32_t         sdigit_t;       // Signed 32-bit digit
#else
    #error -- "Unsupported PLATFORM"
#endif

#endif
