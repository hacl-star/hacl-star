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

VALE_DIR 	= ../secure_api/vale/asm
VALE_OBJS 	= $(addprefix $(VALE_DIR)/,sha256_main_i.o \
  sha256-$(MARCH)$(VARIANT).o Vale_Hash_SHA2_256.o \
  vale_aes_glue.o aes-$(MARCH)$(VARIANT).o)

CODE_DIR	= ../code
SOURCES		= \
  $(CODE_DIR)/salsa-family/chacha-c/Chacha20.c \
  $(CODE_DIR)/salsa-family/salsa-c/Salsa20.c \
  $(CODE_DIR)/salsa-family/chacha-vec128-c/Chacha20_Vec128.c \
  $(addprefix $(CODE_DIR)/hash/sha2-c/SHA2_,256.c 384.c 512.c) \
  $(CODE_DIR)/curve25519/x25519-c/Curve25519.c \
  $(CODE_DIR)/ed25519/ed25519-c/Ed25519.c \
  $(CODE_DIR)/poly1305/poly-c/Poly1305_64.c \
  $(CODE_DIR)/hmac/hmac-c/HMAC_SHA2_256.c \
  $(CODE_DIR)/api/aead-c/Chacha20Poly1305.c \
  #$(CODE_DIR)/poly1305/poly-c/AEAD_Poly1305_64.c \

OBJS		= $(patsubst %.c,%.o,$(SOURCES)) $(VALE_OBJS)

INCLUDE_DIRS	= $(foreach c,$(SOURCES),$(dir $(c))) \
  $(CODE_DIR)/salsa-family $(KREMLIN_HOME)/kremlib

CFLAGS		+= $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter

all: libhacl.a

# Note: see
# https://www.gnu.org/software/make/manual/html_node/Archive-Pitfalls.html#Archive-Pitfalls
# for why we are not using libhacl.a($(OBJS))
libhacl.a: $(OBJS)
	$(AR) cr $@ $^

.PRECIOUS: %.o

$(SOURCES):
	$(error "Please run `make -j 8 -C ../code` before invoking this Makefile")
