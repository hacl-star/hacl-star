HACL_HOME=../..
include $(HACL_HOME)/Makefile.common

all: build/runbenchmark

ifeq ($(OS),Windows_NT)
# Cygwin/MSys we require these compilers.
CMAKE_DEFS?=-DCMAKE_C_COMPILER=x86_64-w64-mingw32-gcc.exe -DCMAKE_CXX_COMPILER=x86_64-w64-mingw32-g++.exe -DCMAKE_AR=$(shell which x86_64-w64-mingw32-ar.exe) -DUSE_BCRYPT=ON
endif

.PHONY: build/runbenchmark # Always runs, so CMake figures out all dependencies.
build/runbenchmark: $(wildcard *.cpp *.h CMakeLists.txt)
	mkdir -p $(dir $@) ; \
	cd $(dir $@) ; \
	cmake -DCMAKE_BUILD_TYPE=Release $(CMAKE_DEFS) .. ; \
	$(MAKE) runbenchmark ; \
	./runbenchmark -n 10 ; \
	cd ..
