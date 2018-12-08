# This is the universal Makefile that will build any distribution of EverCrypt.
# - It is copied from hacl-star/providers/dist/Makefile
# - It relies on the KreMLin-generated Makefile.basic and Makefile.include
#
# This Makefile detects whether OpenSSL and BCrypt are enabled automatically. It
# does so by checking for the presence of EverCrypt_OpenSSL.h and
# EverCrypt_BCrypt.h ; as such, it assumes -bundle EverCrypt.OpenSSL and -bundle
# EverCrypt.BCrypt.
#
# This Makefile may (conservatively) link in some Vale assemblies that may end
# up un-needed in the final shared object.
#
# Additionally, this Makefile works out of the box on Linux, OSX and
# Cygwin/MinGW.
#
# The Makefile assumes KREMLIN_HOME and HACL_HOME to be suitably defined. When
# using OpenSSL, it also expects OPENSSL_HOME to be defined.
#
# The Makefile produces:
# - libevercrypt.so, a shared object where unused symbols have been removed
# - libevercrypt.a, a static archive that includes libhacl.a and libkremlib.a

# 1. The usual pseudo auto-configuration

UNAME		= $(shell uname)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -darwin
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC -fstack-check
  VARIANT	= -linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all
else ifeq ($(OS),Windows_NT)
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  VARIANT	= -mingw
  SO		= dll
endif

# 2. Parameters we want to compile with, for the generated Makefile

CFLAGS		+= -Wno-parentheses -g

# 3. Honor configurations

# Backwards-compat
ifneq (,$(MLCRYPTO_HOME))
OPENSSL_HOME 	= $(MLCRYPTO_HOME)/openssl
endif

ifneq (,$(wildcard EverCrypt_OpenSSL.h))
  CFLAGS	+= -I $(OPENSSL_HOME)/include
  LDFLAGS 	+= -L$(OPENSSL_HOME) -lcrypto
ifneq ($(OS),Windows_NT)
  LDFLAGS	+= -ldl -lpthread
endif
  SOURCES	+= evercrypt_openssl.c
endif

ifneq (,$(wildcard EverCrypt_BCrypt.h))
  LDFLAGS	+= -lbcrypt
  SOURCES	+= evercrypt_bcrypt.c
endif

OBJS 		+= $(patsubst %.S,%.o,$(wildcard *-$(MARCH)$(VARIANT).S))

# Note: some distributions (e.g. coco) don't want bytes

ifneq (,$(wildcard EverCrypt_Bytes.h))
  SOURCES	+= evercrypt_bytes.c
endif

include Makefile.basic

$(HACL_A):
	@echo "Please run make in the $(KREMLIN_HOME)/kremlib directory before invoking this Makefile" && false

$(KREMLIB_A):
	@echo "Please run make in the $(HACL_HOME)/code directory before invoking this Makefile" && false

HACL_A 		= $(HACL_HOME)/code/dist/compact/libhacl.a
KREMLIB_A 	= $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

all: libevercrypt.$(SO)

libevercrypt.$(SO): $(OBJS) $(HACL_A) $(KREMLIB_A)
	$(CC) $(CFLAGS) -shared -o $@ $^ $(LDFLAGS)
