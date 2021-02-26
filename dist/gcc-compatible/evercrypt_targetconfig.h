#ifndef __EVERCRYPT_TARGETCONFIG_H
#define __EVERCRYPT_TARGETCONFIG_H

/* References:
 * - https://docs.microsoft.com/en-us/cpp/preprocessor/predefined-macros?view=vs-2017
 * - https://sourceforge.net/p/predef/wiki/Architectures/
 */

enum {
  TARGET_ARCHI_NAME_X86,
  TARGET_ARCHI_NAME_X64,
  TARGET_ARCHI_NAME_ARM7,
  TARGET_ARCHI_NAME_ARM8,
  TARGET_ARCHI_NAME_SYSTEMZ,
  TARGET_ARCHI_NAME_POWERPC64,
  TARGET_ARCHI_NAME_UNKNOWN
};

#define ARCHI_NAME_X86 0

#if __has_include("config.h")
#include "config.h"
#endif

#endif
