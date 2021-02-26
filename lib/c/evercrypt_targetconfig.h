#ifndef __EVERCRYPT_TARGETCONFIG_H
#define __EVERCRYPT_TARGETCONFIG_H

/* References:
 * - https://docs.microsoft.com/en-us/cpp/preprocessor/predefined-macros?view=vs-2017
 * - https://sourceforge.net/p/predef/wiki/Architectures/
 */

enum {
  // TODO: the macros defined in EverCrypt.TargetConfig.h don't extract as
  // uppercase - fix that
  target_architecture_name_x86,
  target_architecture_name_x64,
  target_architecture_name_arm7,
  target_architecture_name_arm8,
  target_architecture_name_systemz,
  target_architecture_name_powerpc64,
  target_architecture_name_unknown
};

#if __has_include("config.h")
#include "config.h"
#else
#define target_architecture target_architecture_name_unknown
#endif

#endif
