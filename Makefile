#
# Main HACL* Makefile
#

.PHONY: display verify clean

all: display

display:
	@echo "HaCl* Makefile:"
	@echo "- 0 - 'make verify' will run F* verification on all specs, code and secure-api directories"
	@echo "- 1 - 'make verify-specs' will run F* verification on the specifications"
	@echo "- 2 - 'make verify-code' will run F* verification on the code against the specification"
	@echo "- 3 - 'make extract' will generate all the C code and test it (no verification)"
	@echo "- 4 - 'make build' will generate both static and shared libraries (no verification)"
	@echo "- 5 - 'make prepare' will install F* and Kremlin (Requirements are still needed)"


#
# Verification targets
#

extract:
	$(MAKE) -C test snapshot

%.verify-dir: %
	$(MAKE) -C $^ verify

verify-specs: specs.verify-dir
verify-code: code.verify-dir
verify: code.verify-dir secure_api.verify-dir specs.verify-dir

clean:
	@echo $(CYAN)"# Clean HaCl*"$(NORMAL)
	rm -rf *~
	rm -rf build
	rm -rf build-experimental
	$(MAKE) -C specs clean
	$(MAKE) -C code clean
	$(MAKE) -C secure_api clean
	$(MAKE) -C apps clean
	$(MAKE) -C test clean


#
# Undocumented targets (voluntarily)
#

include Makefile.build

build:
	@echo $(CYAN)"# Compiling the HaCl* library"$(NORMAL)
	mkdir -p build && cd build; \
	c$(MAKE) $(CMAKE_COMPILER_OPTION) .. && make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build'."$(NORMAL)

experimental:
	@echo $(CYAN)"# Compiling the HaCl* library (with experimental features)"$(NORMAL)
	mkdir -p build-experimental && cd build-experimental; \
	c$(MAKE) $(CMAKE_COMPILER_OPTION) -DExperimental=ON .. && make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build-experimental'."$(NORMAL)

hints:
	$(MAKE) -C code hints
	$(MAKE) -C secure_api hints
	$(MAKE) -C specs hints
	$(MAKE) -C test hints

refresh-hints:
	$(MAKE) -B hints



# Check if GCC-7 is installed, uses GCC otherwise
GCC_EXEC := $(shell gcc-7 --version 2>/dev/null | cut -c -5 | head -n 1)
ifdef GCC_EXEC
   CMAKE_COMPILER_OPTION := -DCMAKE_C_COMPILER=gcc-7
endif

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
