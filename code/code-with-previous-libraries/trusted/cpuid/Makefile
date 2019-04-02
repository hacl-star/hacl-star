KREMLIN  ?= $(KREMLIN_HOME)/krml

# Check if GCC-6 is installed, uses GCC otherwise
COMPILER := $(shell gcc-7 --version 2>/dev/null | cut -c -5 | head -n 1)
ifdef GCC_EXEC
   CMAKE_COMPILER_OPTION := gcc-7
else
	CMAKE_COMPILER_OPTION := gcc
endif


# Project
EXTERNAL_CODE   = c
BUILD_DIR		 = build

MODULES_ASSUMED = Hacl.Hardware.Intel.CPUID.Assumed
MODULE          = Hacl.Hardware.Intel.CPUID
MAIN            = Test.Hacl.Hardware.Intel.CPUID

INCLUDES        = $(KREMLIN_HOME)/include
EXTRACTED_FILES = cpuid.c Hacl_Hardware_Intel_CPUID.c Test_Hacl_Hardware_Intel_CPUID.c
# Prims.c FStar.c


# Targets
.PHONY: extract-c build clean

all: extract-c build

extract-c:
	@echo $(CYAN)"\n# Generating C code from KreMLin."$(NORMAL)
	krml -minimal $(MAIN).fst -drop Prims,FStar.* -drop $(MODULES_ASSUMED) -tmpdir $(BUILD_DIR) -no-prefix $(MODULES_ASSUMED) -no-prefix $(MODULE) -no-prefix $(MAIN) -add-include '"cpuid.h"' -add-include '"stdlib.h"' -add-include '"stdio.h"' -add-include '"stdbool.h"' -add-include '"inttypes.h"' -add-include '"kremlin/c.h"' -add-include '"kremlin/c_string.h"' -I $(KREMLIN_HOME)/include -skip-compilation


build:
	@echo $(CYAN)"\n# Compiling the CPUID component."$(NORMAL)
	cp $(EXTERNAL_CODE)/* $(BUILD_DIR)
	cd $(BUILD_DIR) && \
	$(CC) $(EXTRACTED_FILES) -I$(INCLUDES) -o test

test:
	@echo $(CYAN)"\n# Run the CPUID test."$(NORMAL)
	@$(BUILD_DIR)/test

clean:
	@echo $(CYAN)"\n# Clean temporary files."$(NORMAL)
	rm -rf *~
	rm -rf $(BUILD_DIR)

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
