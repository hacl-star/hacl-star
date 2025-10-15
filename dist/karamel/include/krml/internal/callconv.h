/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 and MIT Licenses. */

#ifndef KRML_HEADER_CALLCONV_H
#define KRML_HEADER_CALLCONV_H

/******************************************************************************/
/* Some macros to ease compatibility (TODO: move to miTLS)                    */
/******************************************************************************/

/* We want to generate __cdecl safely without worrying about it being undefined.
 * When using MSVC, these are always defined. When using MinGW, these are
 * defined too. They have no meaning for other platforms, so we define them to
 * be empty macros in other situations. */
#ifndef _MSC_VER
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

#endif /* KRML_HEADER_CALLCONV_H */
