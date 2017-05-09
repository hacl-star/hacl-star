HACL_HOME?=..
KREMLIN_HOME?=$(HACL_HOME)/kremlin
FSTAR_HOME?=$(HACL_HOME)/kremlin

.PHONY: snapshot

HAS_CL=$(shell which cl.exe >/dev/null 2>&1 && echo true || echo false)
HAS_CCOMP=$(shell which ccomp >/dev/null 2>&1 && echo true || echo false)

SNAPSHOT_DIR=snapshot

all:
	if $(HAS_CCOMP); then $(MAKE) extract-c KREMLIN_ARGS="-cc compcert"; fi
	if $(HAS_CL); then $(MAKE) extract-c KREMLIN_ARGS="-cc msvc"; fi
	$(MAKE) extract-c
	$(MAKE) ct
	$(MAKE) verify
	$(MAKE) -C openssl-engine

travis:
	$(MAKE) extract-c
	$(MAKE) ct
	$(MAKE) -C .. world

extract-c-code:
	$(MAKE) -C $(HACL_HOME)/code extract-c

extract-c-code-experimental:
	$(MAKE) -C $(HACL_HOME)/code/experimental/ extract-c

extract-c-crypto:
	$(MAKE) -C ../secure_api krml-test-vale.exe
	$(MAKE) -C ../secure_api krml-test-hacl.exe

extract-c: extract-c-code extract-c-crypto

ct:
	$(MAKE) -C ../code ct

verify-code:
	$(MAKE) -C ../code ci

verify-crypto:
	# Note: the all-hints target fails silently.
	$(MAKE) -C ../secure_api all-ver OTHERFLAGS="--record_hints"

hints-code:
	$(MAKE) -C ../code hints

hints-crypto:
	$(MAKE) -C ../secure_api all-hints

hints: hints-code hints-crypto

verify: verify-code verify-crypto

build-snapshot:
	mkdir -p $(SNAPSHOT_DIR)
	cp $(addprefix ../code/poly1305/poly-c/, Poly1305_64.* AEAD_Poly1305_64.*) \
		../code/curve25519/x25519-c/Curve25519.* \
		../code/salsa-family/chacha-c/Chacha20.* \
		../code/salsa-family/salsa-c/Salsa20.* \
		$(addprefix ../code/api/aead-c/, Chacha20Poly1305.*) \
		$(addprefix ../code/api/box-c/, Hacl_Policies.* NaCl.*) \
		$(addprefix ../code/experimental/ed25519/ed25519-c/, Ed25519.*) \
		$(addprefix ../code/experimental/hash/sha2-c/, SHA2_512.*) \
		$(addprefix ../code/experimental/salsa-family/chacha-vec128/, Chacha20_Vec128.* ../vec128.h) \
		 $(SNAPSHOT_DIR)
	cp ./c/* $(SNAPSHOT_DIR)/

CCOMP=gcc-6 -flto -std=c11 -D_GNU_SOURCE

test-snapshot:
	$(MAKE) -C snapshot CC="$(CCOMP)" test

snapshot:
	$(MAKE) extract-c-code extract-c-code-experimental
	$(MAKE) build-snapshot
	$(MAKE) test-snapshot

all-snapshots:
	if $(HAS_CCOMP); then $(MAKE) extract-c-code extract-c-code-experimental KREMLIN_ARGS="-cc compcert -funroll-loops 10"; fi
	if $(HAS_CCOMP); then $(MAKE) build-snapshot SNAPSHOT_DIR=snapshot-ccomp; fi
	$(MAKE) -C ../code clean
	if $(HAS_CL); then $(MAKE) extract-c-code extract-c-code-experimental KREMLIN_ARGS="-cc msvc"; fi
	if $(HAS_CL); then $(MAKE) build-snapshot SNAPSHOT_DIR=snapshot-msvc; fi
	$(MAKE) -C ../code clean
	$(MAKE) extract-c-code extract-c-code-experimental
	$(MAKE) build-snapshot SNAPSHOT_DIR=snapshot-gcc
	$(MAKE) -C ../code clean
	$(MAKE) extract-c-code extract-c-code-experimental KREMLIN_ARGS="-funroll-loops 5"
	$(MAKE) build-snapshot SNAPSHOT_DIR=snapshot-gcc-unrolled
	$(MAKE) -C ../code clean

update-snapshot:
	$(build-snapshot)
	$(MAKE) -C snapshot clean
	cp snapshot/*.c snapshot/*.h ../snapshots/hacl-c

clean:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../secure_api clean
	rm -rf snapshot snapshot-ccomp snapshot-msvc snapshot-gcc *.o *.exe *~
