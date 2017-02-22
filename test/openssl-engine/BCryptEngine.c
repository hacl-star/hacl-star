#include "BCryptWrapper.h"

// This file contains the implementation of the X25519 operation using the CNG
// (modern) Windows Cryptographic APIs. Since Curve25519 is Windows-10 only, and
// since mingw exposes the Windows SDK headers circa 8.1 (which do NOT
// contain the APIs we want), the missing defines are brutally copy-pasted here.
#define BCRYPT_ECDH_ALGORITHM                   L"ECDH"
#define BCRYPT_ECC_CURVE_NAME       L"ECCCurveName"
#define BCRYPT_ECC_CURVE_25519              L"curve25519"

// An alternative is to drop any use of a function from the C runtime system
// (e.g. printf and friends), and compile the present file with MSVC, as
// follows:
//   cl /c /FoBCryptWrapper.o /I"c:/Program Files (x86)/Windows Kits/10/Include/10.0.14393.0/shared" BCryptWrapper.c /link /nod:msvcrt14.lib msvcrt.lib
//
// Then, MinGW will link the object file happily, in spite of a spurious
// warning:
//   Warning: corrupt .drectve at end of def file
//
// Barry says:
// > The .drective warning is from the mingw linker complaining that it couldn't
//   support metadata embedded inside a .obj or .lib file.  Likely something like
//   a Win10 manifest record and ignorable.
// > The error message text is completely misleading.

int X25519(uint8_t *out_shared_key, uint8_t *private_key,
  const uint8_t *peer_public_value) {
  printf("Not implemented");
  exit(255);
}

void initialize_bcrypt() {
  static BCRYPT_ALG_HANDLE hAlg = NULL;
  if (!NT_SUCCESS(BCryptOpenAlgorithmProvider(&hAlg, BCRYPT_ECDH_ALGORITHM, NULL, 0))) {
    fprintf(stderr, "Cannot open algorithm provider");
    exit(1);
  }
  if (!NT_SUCCESS(BCryptSetProperty(hAlg,
          BCRYPT_ECC_CURVE_NAME,
          (PUCHAR) BCRYPT_ECC_CURVE_25519,
          sizeof(BCRYPT_ECC_CURVE_25519),
          0))) {
    fprintf(stderr, "Cannot select the right curve");
    exit(1);
  }

}
