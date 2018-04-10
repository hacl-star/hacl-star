FSTAR_HOME	?= ../../FStar
KREMLIN_HOME	?= ../../kremlin

UNAME		= $(shell uname)
SED		= $(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -Darwin
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC
  VARIANT	= -Linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack
else ifeq ($(OS),Windows_NT)
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  SO		= dll
endif

CODE_DIR	= ../code

SALSA_SOURCES	= \
  $(CODE_DIR)/salsa-family/chacha-c/Chacha20.c \
  $(CODE_DIR)/salsa-family/salsa-c/Salsa20.c \
  $(CODE_DIR)/salsa-family/chacha-vec128-c/Chacha20_Vec128.c

SHA_SOURCES	= \
  $(addprefix $(CODE_DIR)/hash/sha2-c/SHA2_,256.c 384.c 512.c)

CURVE_SOURCES	= \
  $(CODE_DIR)/curve25519/x25519-c/Curve25519.c

ED_SOURCES	= \
  $(CODE_DIR)/ed25519/ed25519-c/Ed25519.c

POLY_SOURCES	= \
  $(CODE_DIR)/poly1305/poly-c/Poly1305_64.c \
  $(CODE_DIR)/poly1305/poly-c/AEAD_Poly1305_64.c

HMAC_SOURCES	= \
  $(CODE_DIR)/hmac/hmac-c/HMAC_SHA2_256.c

AEAD_SOURCES	= \
  $(CODE_DIR)/api/aead-c/Chacha20Poly1305.c


VALE_DIR 	= ../secure_api/vale/asm
VALE_OBJS 	= $(addprefix $(VALE_DIR)/,sha256_main_i.o \
  sha256-$(MARCH)$(VARIANT).o Vale_Hash_SHA2_256.o \
  vale_aes_glue.o aes-$(MARCH)$(VARIANT).o)

SOURCES		= $(SALSA_SOURCES) $(SHA_SOURCES) $(ED_SOURCES) $(POLY_SOURCES) \
  $(HMAC_SOURCES) # $(AEAD_SOURCES)
OBJS		= $(patsubst %.c,%.o,$(SOURCES)) $(VALE_OBJS)
INCLUDE_DIRS	= $(foreach c,$(SOURCES),$(dir $(c))) \
  $(CODE_DIR)/salsa-family $(KREMLIN_HOME)/kremlib

CFLAGS		+= $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter

all: libhacl.a

.PRECIOUS: %.o

# Note: see
# https://www.gnu.org/software/make/manual/html_node/Archive-Pitfalls.html#Archive-Pitfalls
# for why we are not using libhacl.a($(OBJS))
libhacl.a: $(OBJS)
	$(AR) cr $@ $^

.PHONY: $(SALSA_SOURCES)
$(SALSA_SOURCES):
	$(MAKE) -C $(CODE_DIR)/salsa-family extract-c

.PHONY: $(SHA_SOURCES)
$(SHA_SOURCES):
	$(MAKE) -C $(CODE_DIR)/hash extract-c

.PHONY: $(CURVE_SOURCES)
$(CURVE_SOURCES):
	$(MAKE) -C $(CODE_DIR)/curve25519 extract-c

.PHONY: $(ED_SOURCES)
$(ED_SOURCES):
	$(MAKE) -C $(CODE_DIR)/ed25519 extract-c

.PHONY: $(POLY_SOURCES)
$(POLY_SOURCES):
	$(MAKE) -C $(CODE_DIR)/poly1305 extract-c

.PHONY: $(HMAC_SOURCES)
$(HMAC_SOURCES):
	$(MAKE) -C $(CODE_DIR)/hmac extract-c

.PHONY: $(AEAD_SOURCES)
$(AEAD_SOURCES):
	$(MAKE) -C $(CODE_DIR)/api extract-c
