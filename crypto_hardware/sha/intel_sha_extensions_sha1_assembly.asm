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
; Intel SHA Extensions optimized implementation of a SHA-1 update function 
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Example YASM command lines:
; Windows:  
;  yasm -Xvc -f x64 -rnasm -pnasm -DWINABI -o intel_sha_extensions_sha1_assembly.obj -g cv8 intel_sha_extensions_sha1_assembly.asm
; Linux:    
;  yasm -f elf64 -X gnu -g dwarf2 -o intel_sha_extensions_sha1_assembly.o intel_sha_extensions_sha1_assembly.asm
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

%define RSPSAVE		rax

struc frame
%ifdef WINABI
.xmm_save:	resdq	2
%endif
.hash_save:	resdq	2
endstruc

%define ABCD		xmm0
%define E0		xmm1	; Need two E's b/c they ping pong
%define E1		xmm2
%define MSG0		xmm3
%define MSG1		xmm4
%define MSG2		xmm5
%define MSG3		xmm6
%define SHUF_MASK	xmm7

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; void sha1_update(uint32_t *digest, const void *data, uint32_t numBlocks);
;; arg 1 : pointer to digest
;; arg 2 : pointer to input data
;; arg 3 : Number of blocks to process
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
section .text
global sha1_update:function
align 32
sha1_update:
	mov		RSPSAVE, rsp
	sub		rsp, frame_size
	and		rsp, ~0xF

%ifdef WINABI
	movdqa		[rsp + frame.xmm_save + 0*16], xmm6
	movdqa		[rsp + frame.xmm_save + 1*16], xmm7
%endif

	shl		NUM_BLKS, 6		; convert to bytes
	jz		.done_hash
	add		NUM_BLKS, DATA_PTR	; pointer to end of data

	;; load initial hash values
	pinsrd		E0,   [DIGEST_PTR + 1*16], 3
	movdqu		ABCD, [DIGEST_PTR + 0*16]
	pand		E0,   [UPPER_WORD_MASK wrt rip]
	pshufd		ABCD, ABCD, 0x1B

	movdqa		SHUF_MASK, [PSHUFFLE_BYTE_FLIP_MASK wrt rip]

.loop0:
	;; Save hash values for addition after rounds
	movdqa		[rsp + frame.hash_save + 0*16], E0
	movdqa		[rsp + frame.hash_save + 1*16], ABCD

	;; Rounds 0-3
	movdqu		MSG0, [DATA_PTR + 0*16]
	pshufb		MSG0, SHUF_MASK
		paddd		E0, MSG0
		movdqa		E1, ABCD
		sha1rnds4	ABCD, E0, 0

	;; Rounds 4-7
	movdqu		MSG1, [DATA_PTR + 1*16]
	pshufb		MSG1, SHUF_MASK
		sha1nexte	E1, MSG1
		movdqa		E0, ABCD
		sha1rnds4	ABCD, E1, 0
	sha1msg1	MSG0, MSG1

	;; Rounds 8-11
	movdqu		MSG2, [DATA_PTR + 2*16]
	pshufb		MSG2, SHUF_MASK
		sha1nexte	E0, MSG2
		movdqa		E1, ABCD
		sha1rnds4	ABCD, E0, 0
	sha1msg1	MSG1, MSG2
	pxor		MSG0, MSG2

	;; Rounds 12-15
	movdqu		MSG3, [DATA_PTR + 3*16]
	pshufb		MSG3, SHUF_MASK
		sha1nexte	E1, MSG3
		movdqa		E0, ABCD
	sha1msg2	MSG0, MSG3
		sha1rnds4	ABCD, E1, 0
	sha1msg1	MSG2, MSG3
	pxor		MSG1, MSG3

	;; Rounds 16-19
		sha1nexte	E0, MSG0
		movdqa		E1, ABCD
	sha1msg2	MSG1, MSG0
		sha1rnds4	ABCD, E0, 0
	sha1msg1	MSG3, MSG0
	pxor		MSG2, MSG0
	
	;; Rounds 20-23
		sha1nexte	E1, MSG1
		movdqa		E0, ABCD
	sha1msg2	MSG2, MSG1
		sha1rnds4	ABCD, E1, 1
	sha1msg1	MSG0, MSG1
	pxor		MSG3, MSG1
	
	;; Rounds 24-27
		sha1nexte	E0, MSG2
		movdqa		E1, ABCD
	sha1msg2	MSG3, MSG2
		sha1rnds4	ABCD, E0, 1
	sha1msg1	MSG1, MSG2
	pxor		MSG0, MSG2
	
	;; Rounds 28-31
		sha1nexte	E1, MSG3
		movdqa		E0, ABCD
	sha1msg2	MSG0, MSG3
		sha1rnds4	ABCD, E1, 1
	sha1msg1	MSG2, MSG3
	pxor		MSG1, MSG3

	;; Rounds 32-35
		sha1nexte	E0, MSG0
		movdqa		E1, ABCD
	sha1msg2	MSG1, MSG0
		sha1rnds4	ABCD, E0, 1
	sha1msg1	MSG3, MSG0
	pxor		MSG2, MSG0
	
	;; Rounds 36-39
		sha1nexte	E1, MSG1
		movdqa		E0, ABCD
	sha1msg2	MSG2, MSG1
		sha1rnds4	ABCD, E1, 1
	sha1msg1	MSG0, MSG1
	pxor		MSG3, MSG1
	
	;; Rounds 40-43
		sha1nexte	E0, MSG2
		movdqa		E1, ABCD
	sha1msg2	MSG3, MSG2
		sha1rnds4	ABCD, E0, 2
	sha1msg1	MSG1, MSG2
	pxor		MSG0, MSG2
	
	;; Rounds 44-47
		sha1nexte	E1, MSG3
		movdqa		E0, ABCD
	sha1msg2	MSG0, MSG3
		sha1rnds4	ABCD, E1, 2
	sha1msg1	MSG2, MSG3
	pxor		MSG1, MSG3

	;; Rounds 48-51
		sha1nexte	E0, MSG0
		movdqa		E1, ABCD
	sha1msg2	MSG1, MSG0
		sha1rnds4	ABCD, E0, 2
	sha1msg1	MSG3, MSG0
	pxor		MSG2, MSG0
	
	;; Rounds 52-55
		sha1nexte	E1, MSG1
		movdqa		E0, ABCD
	sha1msg2	MSG2, MSG1
		sha1rnds4	ABCD, E1, 2
	sha1msg1	MSG0, MSG1
	pxor		MSG3, MSG1
	
	;; Rounds 56-59
		sha1nexte	E0, MSG2
		movdqa		E1, ABCD
	sha1msg2	MSG3, MSG2
		sha1rnds4	ABCD, E0, 2
	sha1msg1	MSG1, MSG2
	pxor		MSG0, MSG2
	
	;; Rounds 60-63
		sha1nexte	E1, MSG3
		movdqa		E0, ABCD
	sha1msg2	MSG0, MSG3
		sha1rnds4	ABCD, E1, 3
	sha1msg1	MSG2, MSG3
	pxor		MSG1, MSG3

	;; Rounds 64-67
		sha1nexte	E0, MSG0
		movdqa		E1, ABCD
	sha1msg2	MSG1, MSG0
		sha1rnds4	ABCD, E0, 3
	sha1msg1	MSG3, MSG0
	pxor		MSG2, MSG0
	
	;; Rounds 68-71
		sha1nexte	E1, MSG1
		movdqa		E0, ABCD
	sha1msg2	MSG2, MSG1
		sha1rnds4	ABCD, E1, 3
	pxor		MSG3, MSG1
	
	;; Rounds 72-75
		sha1nexte	E0, MSG2
		movdqa		E1, ABCD
	sha1msg2	MSG3, MSG2
		sha1rnds4	ABCD, E0, 3
	
	;; Rounds 76-79
		sha1nexte	E1, MSG3
		movdqa		E0, ABCD
		sha1rnds4	ABCD, E1, 3

	;; Add current hash values with previously saved
	sha1nexte	E0,   [rsp + frame.hash_save + 0*16]
	paddd		ABCD, [rsp + frame.hash_save + 1*16]

	;; Increment data pointer and loop if more to process
	add		DATA_PTR, 64
	cmp		DATA_PTR, NUM_BLKS
	jne		.loop0

	;; Write hash values back in the correct order
	pshufd		ABCD, ABCD, 0x1B
	movdqu		[DIGEST_PTR + 0*16], ABCD
	pextrd		[DIGEST_PTR + 1*16], E0, 3

.done_hash:
%ifdef WINABI
	movdqa		xmm6, [rsp + frame.xmm_save + 0*16]
	movdqa		xmm7, [rsp + frame.xmm_save + 1*16]
%endif
	mov		rsp, RSPSAVE

	ret	

section .data
align 64
PSHUFFLE_BYTE_FLIP_MASK: ddq 0x000102030405060708090a0b0c0d0e0f
UPPER_WORD_MASK:         ddq 0xFFFFFFFF000000000000000000000000

