#include "asmopt_internal.h"

#if defined(_WIN32) || defined(__CYGWIN__)

#include <windows.h>

BOOL WINAPI DllMain(HINSTANCE hinstDLL, DWORD fdwReason, LPVOID lpvReserved) {
	hinstDLL;
	lpvReserved;

	switch (fdwReason) {
		case DLL_PROCESS_ATTACH:
			break;

		case DLL_THREAD_ATTACH:
			break;

		case DLL_THREAD_DETACH:
			break;

		case DLL_PROCESS_DETACH:
			break;
	}

	return TRUE;
}

#endif /* defined(_WIN32) || defined(__CYGWIN__) */
