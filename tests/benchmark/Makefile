ifeq ($(OS),Windows_NT)
HACL_HOME=$(shell cygpath -u -a ../..)
else
HACL_HOME=$(shell realpath ../..)
endif

include $(HACL_HOME)/Makefile.common

all: build/runbenchmark

CMAKE_DEFS+=\
	-DEVERCRYPT_SRC_DIR=$(HACL_HOME)/dist/gcc64-only \
	-DKREMLIN_INC=$(KREMLIN_HOME)/include \
	-DKREMLIB_DIR=$(KREMLIN_HOME)/kremlib/dist/generic \
	-DRFC7748_DIR=$(HACL_HOME)/tests/rfc7748_src

ifeq ($(OS),Windows_NT)
# On Cygwin/MSys we require these compilers. The version of cmake that currently comes with Cygwin needs -DCMAKE_AR with a full path to the binary.
CMAKE_DEFS+=-DCMAKE_C_COMPILER=x86_64-w64-mingw32-gcc.exe -DCMAKE_CXX_COMPILER=x86_64-w64-mingw32-g++.exe -DCMAKE_AR=$(shell which x86_64-w64-mingw32-ar.exe) -DUSE_BCRYPT=ON
else
CMAKE_DEFS+=-DCMAKE_C_COMPILER=$(CC) -DCMAKE_CXX_COMPILER=$(CXX)
endif

.PHONY: build/runbenchmark # Always runs, so CMake figures out all dependencies.
build/runbenchmark:
	mkdir -p $(dir $@) && \
	cd $(dir $@) && \
	cmake -DCMAKE_BUILD_TYPE=Release $(CMAKE_DEFS) .. &&  \
	$(MAKE) runbenchmark && \
	./runbenchmark -n 10 && \
	cd ..
