# This is the universal Makefile that will build any distribution of EverCrypt.
# - It is copied from hacl-star/providers/dist/Makefile
# - It relies on the KreMLin-generated Makefile.basic and Makefile.include
#
# This Makefile can be parameterized using four environment variables:
# - EVERCRYPT_OPENSSL (default = true)
# - EVERCRYPT_BCRYPT (default = false)
# - EVERCRYPT_VALE (default = true)
# - EVERCRYPT_HACL (default = true, currently unused)
# Each variable triggers the right: extra C files, extra ASM files, compiler and
# linker flags.
#
# Additionally, this Makefile works out of the box on Linux, OSX and
# Cygwin/MinGW.
#
# The Makefile assumes KREMLIN_HOME and HACL_HOME to be suitably defined. When
# using EVERCRYPT_OPENSSL=true, it also expects OPENSSL_HOME to be defined.
#
# The Makefile produces:
# - libevercrypt.so, a shared object where unused symbols have been removed
# - libevercrypt.a, a static archive that includes libhacl.a and libkremlib.a

include Makefile.basic

EVERCRYPT_OPENSSL	?= true
EVERCRYPT_BCRYPT	?= false
EVERCRYPT_VALE		?= true
EVERCRYPT_HACL		?= true

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

ifeq ($(EVERCRYPT_OPENSSL),true)
  CFLAGS	+= -I $(OPENSSL_HOME)/include
  LDFLAGS 	+= -L$(OPENSSL_HOME) -lcrypto
  LDFLAGS	+= -ldl -lpthread
  USER_C_FILES	+= evercrypt_openssl.c
endif

ifeq ($(EVERCRYPT_BCRYPT),true)
  LDFLAGS	+= -lbcrypt
  USER_C_FILES	+= evercrypt_bcrypt.c
endif

ifeq ($(EVERCRYPT_VALE),true)
  OBJS 		+= $(patsubst %.S,%.o,$(wildcard *-$(MARCH)$(VARIANT).S))
endif

$(HACL_A):
	@echo "Please run make in the $(KREMLIN_HOME)/kremlib directory before invoking this Makefile" && false

$(KREMLIB_A):
	@echo "Please run make in the $(HACL_HOME)/code directory before invoking this Makefile" && false

HACL_A 		= $(HACL_HOME)/code/dist/compact/libhacl.a
KREMLIB_A 	= $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

all: libevercrypt.$(SO)

libevercrypt.$(SO): $(OBJS) $(HACL_A) $(KREMLIB_A)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ $^
