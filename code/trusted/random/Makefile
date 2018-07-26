KREMLIN  ?= $(KREMLIN_HOME)/krml

# Check if GCC-6 is installed, uses GCC otherwise
COMPILER := $(shell gcc-7 --version 2>/dev/null | cut -c -5 | head -n 1)
ifdef GCC_EXEC
   CMAKE_COMPILER_OPTION := gcc-7
else
	CMAKE_COMPILER_OPTION := gcc
endif



# Dependencies
CPUID_DIR         = ../cpuid
CPUID_ASSUMED_DIR = ../cpuid/c

# Project
EXTERNAL_CODE   = c
BUILD_DIR		 = build

MODULES_ASSUMED = Hacl.Trusted.Random.Hardware.Assumed
MODULE          = Hacl.Trusted.Random.Hardware
MAIN            = Hacl.Test.Trusted.Random.Hardware

INCLUDES        = $(KREMLIN_HOME)/kremlib/compat
EXTRACTED_FILES =  Prims.c FStar.c cpuid.c drng.c Hacl_Trusted_Random_Hardware.c Hacl_Test_Trusted_Random_Hardware.c


# Targets
.PHONY: extract-c build clean

all: extract-c build

extract-c:
	@echo $(CYAN)"\n# Generating C code from KreMLin."$(NORMAL)
	krml $(MAIN).fst -drop Hacl.Hardware.Intel.CPUID.Assumed -drop Hacl.Hardware.Intel.CPUID -drop $(MODULES_ASSUMED) -tmpdir $(BUILD_DIR) -no-prefix $(MODULES_ASSUMED) -no-prefix $(MODULE) -no-prefix $(MAIN) -add-include '"config.h"' -add-include '"drng.h"' -add-include '"../../cpuid/c/cpuid.h"' -skip-compilation


build:
	@echo $(CYAN)"\n# Compiling the DRNG component."$(NORMAL)
	cp $(EXTERNAL_CODE)/* $(BUILD_DIR)
	cp $(CPUID_ASSUMED_DIR)/cpuid.{c,h} $(BUILD_DIR)
	cd $(BUILD_DIR) && \
	$(COMPILER) $(KREMLIN_HOME)/kremlib/kremlib.c $(EXTRACTED_FILES) -I$(INCLUDES) -o test

test:
	@echo $(CYAN)"\n# Run the DRNG test."$(NORMAL)
	@$(BUILD_DIR)/test

clean:
	@echo $(CYAN)"\n# Clean temporary files."$(NORMAL)
	rm -rf *~
	rm -rf $(BUILD_DIR)

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
