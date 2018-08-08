#ifndef __AES_H
#define __AES_H

// gcc does not support the __stdcall notation
#include "gcc_compat.h"

// These are the Vale entrypoints
void __stdcall KeyExpansionStdcall(const void * key_ptr, void *expanded_key_ptr);
void __stdcall KeyExpansionAndInversionStdcall();
void __stdcall AES128EncryptOneBlockStdcall(void *output_ptr, const void *input_ptr, const void *expanded_key_ptr);

#endif // __AES_H
