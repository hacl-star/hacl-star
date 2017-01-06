;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Copyright (c) 2013, Intel Corporation 
; 
; All rights reserved. 
; 
; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met: 
; 
; * Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.  
; 
; * Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the
;   distribution. 
; 
; * Neither the name of the Intel Corporation nor the names of its
;   contributors may be used to endorse or promote products derived from
;   this software without specific prior written permission. 
; 
; 
; THIS SOFTWARE IS PROVIDED BY INTEL CORPORATION ""AS IS"" AND ANY
; EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
; PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL INTEL CORPORATION OR
; CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
; EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
; PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
; PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
; LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Intel SHA Extensions optimized implementation of a SHA-256 update function 
;
; The function takes a pointer to the current hash values, a pointer to the 
; input data, and a number of 64 byte blocks to process.  Once all blocks have 
; been processed, the digest pointer is  updated with the resulting hash value.
; The function only processes complete blocks, there is no functionality to 
; store partial blocks.  All message padding and hash value initialization must
; be done outside the update function.  
;
; The indented lines in the loop are instructions related to rounds processing.
; The non-indented lines are instructions related to the message schedule.
;
; Author: Sean Gulley <sean.m.gulley@intel.com>
; Date:   July 2013
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Example YASM command lines:
; Windows:  yasm -Xvc -f x64 -rnasm -pnasm -DWINABI -o intel_sha_extensions_sha256_assembly.obj -g cv8 intel_sha_extensions_sha256_assembly.asm
; Linux:    yasm -f elf64 -X gnu -g dwarf2 -o intel_sha_extensions_sha256_assembly.o intel_sha_extensions_sha256_assembly.asm
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

%ifdef WINABI
%define DIGEST_PTR	rcx 	; 1st arg
%define DATA_PTR	rdx 	; 2nd arg
%define NUM_BLKS 	r8	; 3rd arg
%else
%define DIGEST_PTR	rdi	; 1st arg
%define DATA_PTR	rsi	; 2nd arg
%define NUM_BLKS	rdx	; 3rd arg
%endif

%define SHA256CONSTANTS	rax

%ifdef WINABI
%define RSPSAVE		r9

struc frame
.xmm_save:	resdq	5
endstruc
%endif

%define MSG		xmm0
%define STATE0		xmm1
%define STATE1		xmm2
%define MSGTMP0		xmm3
%define MSGTMP1		xmm4
%define MSGTMP2		xmm5
%define MSGTMP3		xmm6
%define MSGTMP4		xmm7

%define SHUF_MASK	xmm8

%define ABEF_SAVE	xmm9
%define CDGH_SAVE	xmm10

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; void sha256_update(uint32_t *digest, const void *data, uint32_t numBlocks);
;; arg 1 : pointer to digest
;; arg 2 : pointer to input data
;; arg 3 : Number of blocks to process
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
section .text
global sha256_update:function
align 32
sha256_update:
%ifdef WINABI
	mov		RSPSAVE, rsp
	sub		rsp, frame_size
	and		rsp, ~0xF

	movdqa		[rsp + frame.xmm_save + 0*16], xmm6
	movdqa		[rsp + frame.xmm_save + 1*16], xmm7
	movdqa		[rsp + frame.xmm_save + 2*16], xmm8
	movdqa		[rsp + frame.xmm_save + 3*16], xmm9
	movdqa		[rsp + frame.xmm_save + 4*16], xmm10
%endif

	shl		NUM_BLKS, 6		; convert to bytes
	jz		.done_hash
	add		NUM_BLKS, DATA_PTR	; pointer to end of data

	;; load initial hash values
	;; Need to reorder these appropriately
	;; DCBA, HGFE -> ABEF, CDGH
	movdqu		STATE0, [DIGEST_PTR + 0*16]
	movdqu		STATE1, [DIGEST_PTR + 1*16]

	pshufd		STATE0,  STATE0,  0xB1	; CDAB
	pshufd		STATE1,  STATE1,  0x1B	; EFGH
	movdqa		MSGTMP4, STATE0
	palignr		STATE0,  STATE1,  8	; ABEF
	pblendw		STATE1,  MSGTMP4, 0xF0	; CDGH

	movdqa		SHUF_MASK, [PSHUFFLE_BYTE_FLIP_MASK wrt rip]
	lea		SHA256CONSTANTS,[K256 wrt rip]

.loop0:
	;; Save hash values for addition after rounds
	movdqa		ABEF_SAVE, STATE0
	movdqa		CDGH_SAVE, STATE1

	;; Rounds 0-3
	movdqu		MSG, [DATA_PTR + 0*16]
	pshufb		MSG, SHUF_MASK
	movdqa		MSGTMP0, MSG
		paddd		MSG, [SHA256CONSTANTS + 0*16]
		sha256rnds2	STATE1, STATE0
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1

	;; Rounds 4-7
	movdqu		MSG, [DATA_PTR + 1*16]
	pshufb		MSG, SHUF_MASK
	movdqa		MSGTMP1, MSG
		paddd		MSG, [SHA256CONSTANTS + 1*16]
		sha256rnds2	STATE1, STATE0
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP0, MSGTMP1

	;; Rounds 8-11
	movdqu		MSG, [DATA_PTR + 2*16]
	pshufb		MSG, SHUF_MASK
	movdqa		MSGTMP2, MSG
		paddd		MSG, [SHA256CONSTANTS + 2*16]
		sha256rnds2	STATE1, STATE0
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP1, MSGTMP2

	;; Rounds 12-15
	movdqu		MSG, [DATA_PTR + 3*16]
	pshufb		MSG, SHUF_MASK
	movdqa		MSGTMP3, MSG
		paddd		MSG, [SHA256CONSTANTS + 3*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP3
	palignr		MSGTMP4, MSGTMP2, 4
	paddd		MSGTMP0, MSGTMP4
	sha256msg2	MSGTMP0, MSGTMP3
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP2, MSGTMP3

	;; Rounds 16-19
	movdqa		MSG, MSGTMP0
		paddd		MSG, [SHA256CONSTANTS + 4*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP0
	palignr		MSGTMP4, MSGTMP3, 4
	paddd		MSGTMP1, MSGTMP4
	sha256msg2	MSGTMP1, MSGTMP0
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP3, MSGTMP0

	;; Rounds 20-23
	movdqa		MSG, MSGTMP1
		paddd		MSG, [SHA256CONSTANTS + 5*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP1
	palignr		MSGTMP4, MSGTMP0, 4
	paddd		MSGTMP2, MSGTMP4
	sha256msg2	MSGTMP2, MSGTMP1
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP0, MSGTMP1

	;; Rounds 24-27
	movdqa		MSG, MSGTMP2
		paddd		MSG, [SHA256CONSTANTS + 6*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP2
	palignr		MSGTMP4, MSGTMP1, 4
	paddd		MSGTMP3, MSGTMP4
	sha256msg2	MSGTMP3, MSGTMP2
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP1, MSGTMP2

	;; Rounds 28-31
	movdqa		MSG, MSGTMP3
		paddd		MSG, [SHA256CONSTANTS + 7*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP3
	palignr		MSGTMP4, MSGTMP2, 4
	paddd		MSGTMP0, MSGTMP4
	sha256msg2	MSGTMP0, MSGTMP3
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP2, MSGTMP3

	;; Rounds 32-35
	movdqa		MSG, MSGTMP0
		paddd		MSG, [SHA256CONSTANTS + 8*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP0
	palignr		MSGTMP4, MSGTMP3, 4
	paddd		MSGTMP1, MSGTMP4
	sha256msg2	MSGTMP1, MSGTMP0
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP3, MSGTMP0

	;; Rounds 36-39
	movdqa		MSG, MSGTMP1
		paddd		MSG, [SHA256CONSTANTS + 9*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP1
	palignr		MSGTMP4, MSGTMP0, 4
	paddd		MSGTMP2, MSGTMP4
	sha256msg2	MSGTMP2, MSGTMP1
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP0, MSGTMP1

	;; Rounds 40-43
	movdqa		MSG, MSGTMP2
		paddd		MSG, [SHA256CONSTANTS + 10*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP2
	palignr		MSGTMP4, MSGTMP1, 4
	paddd		MSGTMP3, MSGTMP4
	sha256msg2	MSGTMP3, MSGTMP2
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP1, MSGTMP2

	;; Rounds 44-47
	movdqa		MSG, MSGTMP3
		paddd		MSG, [SHA256CONSTANTS + 11*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP3
	palignr		MSGTMP4, MSGTMP2, 4
	paddd		MSGTMP0, MSGTMP4
	sha256msg2	MSGTMP0, MSGTMP3
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP2, MSGTMP3

	;; Rounds 48-51
	movdqa		MSG, MSGTMP0
		paddd		MSG, [SHA256CONSTANTS + 12*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP0
	palignr		MSGTMP4, MSGTMP3, 4
	paddd		MSGTMP1, MSGTMP4
	sha256msg2	MSGTMP1, MSGTMP0
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1
	sha256msg1	MSGTMP3, MSGTMP0

	;; Rounds 52-55
	movdqa		MSG, MSGTMP1
		paddd		MSG, [SHA256CONSTANTS + 13*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP1
	palignr		MSGTMP4, MSGTMP0, 4
	paddd		MSGTMP2, MSGTMP4
	sha256msg2	MSGTMP2, MSGTMP1
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1

	;; Rounds 56-59
	movdqa		MSG, MSGTMP2
		paddd		MSG, [SHA256CONSTANTS + 14*16]
		sha256rnds2	STATE1, STATE0
	movdqa		MSGTMP4, MSGTMP2
	palignr		MSGTMP4, MSGTMP1, 4
	paddd		MSGTMP3, MSGTMP4
	sha256msg2	MSGTMP3, MSGTMP2
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1

	;; Rounds 60-63
	movdqa		MSG, MSGTMP3
		paddd		MSG, [SHA256CONSTANTS + 15*16]
		sha256rnds2	STATE1, STATE0
		pshufd 		MSG, MSG, 0x0E
		sha256rnds2	STATE0, STATE1

	;; Add current hash values with previously saved
	paddd		STATE0, ABEF_SAVE
	paddd		STATE1, CDGH_SAVE

	;; Increment data pointer and loop if more to process
	add		DATA_PTR, 64
	cmp		DATA_PTR, NUM_BLKS
	jne		.loop0

	;; Write hash values back in the correct order
	pshufd		STATE0,  STATE0,  0x1B	; FEBA
	pshufd		STATE1,  STATE1,  0xB1	; DCHG
	movdqa		MSGTMP4, STATE0
	pblendw		STATE0,  STATE1,  0xF0	; DCBA
	palignr		STATE1,  MSGTMP4, 8	; HGFE

	movdqu		[DIGEST_PTR + 0*16], STATE0
	movdqu		[DIGEST_PTR + 1*16], STATE1

.done_hash:
%ifdef WINABI
	movdqa		xmm6,  [rsp + frame.xmm_save + 0*16]
	movdqa		xmm7,  [rsp + frame.xmm_save + 1*16]
	movdqa		xmm8,  [rsp + frame.xmm_save + 2*16]
	movdqa		xmm9,  [rsp + frame.xmm_save + 3*16]
	movdqa		xmm10, [rsp + frame.xmm_save + 4*16]
	mov		rsp, RSPSAVE
%endif

	ret	
	
section .data
align 64
K256:
	dd	0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5
	dd	0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5
	dd	0xd807aa98,0x12835b01,0x243185be,0x550c7dc3
	dd	0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174
	dd	0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc
	dd	0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da
	dd	0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7
	dd	0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967
	dd	0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13
	dd	0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85
	dd	0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3
	dd	0xd192e819,0xd6990624,0xf40e3585,0x106aa070
	dd	0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5
	dd	0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3
	dd	0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208
	dd	0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2

PSHUFFLE_BYTE_FLIP_MASK: ddq 0x0c0d0e0f08090a0b0405060700010203

