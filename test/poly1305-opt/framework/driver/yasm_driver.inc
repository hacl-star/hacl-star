%ifndef YASM_DRIVER_INC
%define YASM_DRIVER_INC

%include "asmopt_internal.h"

%include "x86/yasm.inc"

%macro INCLUDE_IF_X86_32BIT 1
	%if (BITS32)
		INCLUDE %1
	%endif
%endmacro

%macro INCLUDE_IF_X86_64BIT 1
	%if (BITS64)
		INCLUDE %1
	%endif
%endmacro

%macro INCLUDE_IF_MMX_32BIT 1
	INCLUDE_IF_X86_32BIT %1
%endmacro

%macro INCLUDE_IF_MMX_64BIT 1
	INCLUDE_IF_X86_64BIT %1
%endmacro


%macro INCLUDE_IF_SSE_32BIT 1
	INCLUDE_IF_X86_32BIT %1
%endmacro

%macro INCLUDE_IF_SSE_64BIT 1
	INCLUDE_IF_X86_64BIT %1
%endmacro


%macro INCLUDE_IF_SSE2_32BIT 1
	INCLUDE_IF_X86_32BIT %1
%endmacro

%macro INCLUDE_IF_SSE2_64BIT 1
	INCLUDE_IF_X86_64BIT %1
%endmacro


%macro INCLUDE_IF_SSE3_32BIT 1
	INCLUDE_IF_X86_32BIT %1
%endmacro

%macro INCLUDE_IF_SSE3_64BIT 1
	INCLUDE_IF_X86_64BIT %1
%endmacro


%macro INCLUDE_IF_SSSE3_32BIT 1
	INCLUDE_IF_X86_32BIT %1
%endmacro

%macro INCLUDE_IF_SSSE3_64BIT 1
	INCLUDE_IF_X86_64BIT %1
%endmacro


%macro INCLUDE_IF_SSE4_1_32BIT 1
	INCLUDE_IF_X86_32BIT %1
%endmacro

%macro INCLUDE_IF_SSE4_1_64BIT 1
	INCLUDE_IF_X86_64BIT %1
%endmacro


%macro INCLUDE_IF_SSE4_2_32BIT 1
	INCLUDE_IF_X86_32BIT %1
%endmacro

%macro INCLUDE_IF_SSE4_2_64BIT 1
	INCLUDE_IF_X86_64BIT %1
%endmacro


%macro INCLUDE_IF_AVX_32BIT 1
	INCLUDE_IF_X86_32BIT %1
%endmacro

%macro INCLUDE_IF_AVX_64BIT 1
	INCLUDE_IF_X86_64BIT %1
%endmacro


%macro INCLUDE_IF_XOP_32BIT 1
	%if HAVE_XOP
		INCLUDE_IF_X86_32BIT %1
	%endif
%endmacro

%macro INCLUDE_IF_XOP_64BIT 1
	%if HAVE_XOP
		INCLUDE_IF_X86_64BIT %1
	%endif
%endmacro


%macro INCLUDE_IF_AVX2_32BIT 1
	%if HAVE_AVX2
		INCLUDE_IF_X86_32BIT %1
	%endif
%endmacro

%macro INCLUDE_IF_AVX2_64BIT 1
	%if HAVE_AVX2
		INCLUDE_IF_X86_64BIT %1
	%endif
%endmacro


%macro INCLUDE_IF_AVX512_32BIT 1
	%if HAVE_AVX512
		INCLUDE_IF_X86_32BIT %1
	%endif
%endmacro

%macro INCLUDE_IF_AVX512_64BIT 1
	%if HAVE_AVX512
		INCLUDE_IF_X86_64BIT %1
	%endif
%endmacro

; include unsupported platform includes here
; ...
; ...
; ...

%endif ; YASM_DRIVER_INC