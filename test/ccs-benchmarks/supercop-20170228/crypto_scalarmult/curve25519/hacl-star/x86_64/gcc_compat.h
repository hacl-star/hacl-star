#ifndef __GCC_COMPAT_H
#define __GCC_COMPAT_H

#ifndef _MSC_VER
  // Use the gcc predefined macros if on a platform/architectures that set them.  Otherwise define them to be empty.
  #ifndef __cdecl
    #define __cdecl
  #endif
  #ifndef __stdcall
    #define __stdcall
  #endif
  #ifndef __fastcall
    #define __fastcall
  #endif
#endif


#endif // __GCC_COMPAT_H
