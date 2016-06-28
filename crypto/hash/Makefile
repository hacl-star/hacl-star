.PHONY: lib-ver sha1-ver sha1-lax sha1-ml sha224-ver sha224-lax sha224-ml sha256-ver sha256-lax sha256-ml sha384-ver sha384-lax sha384-ml sha512-ver sha512-lax sha512-ml

##
#
#  Main targets
#
#

# Default
all: sha1-ml sha224-ml sha256-ml sha384-ml sha512-ml

# Verification target for the low-level libraries
lib-ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES)

# Verification target for SHA-1
sha1-ver:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) Hash.Sha1.fst

# Lax verification target for SHA-1
sha1-lax:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) --lax Hash.Sha1.fst

# Extraction target to OCaml for SHA-1
sha1-ml:
	@echo "Extracting SHA_1 to OCaml"
	mkdir -p $(SHA_ODIR)1_ml
	$(FSTAR) $(OPTIONS_OCAML) --include $(LIB_DIR) Hash.Sha1.fst --odir $(SHA_ODIR)1_ml
	cp ./lib_ml/*.ml $(SHA_ODIR)1_ml

# Verification target for SHA-224
sha224-ver:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) Hash.Sha224.fst

# Lax verification target for SHA-224
sha224-lax:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) --lax Hash.Sha224.fst

# Extraction target to OCaml for SHA-224
sha224-ml:
	@echo "Extracting SHA_224 to OCaml"
	mkdir -p $(SHA_ODIR)224_ml
	$(FSTAR) $(OPTIONS_OCAML) --include $(LIB_DIR) Hash.Sha224.fst --odir $(SHA_ODIR)224_ml
	cp ./lib_ml/*.ml $(SHA_ODIR)224_ml

# Verification target for SHA-256
sha256-ver:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) Hash.Sha256.fst

# Lax verification target for SHA-256
sha256-lax:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) --lax Hash.Sha256.fst

# Extraction target to OCaml for SHA-256
sha256-ml:
	@echo "Extracting SHA_256 to OCaml"
	mkdir -p $(SHA_ODIR)256_ml
	$(FSTAR) $(OPTIONS_OCAML) --include $(LIB_DIR) Hash.Sha256.fst --odir $(SHA_ODIR)256_ml
	cp ./lib_ml/*.ml $(SHA_ODIR)256_ml

# Verification target for SHA-384
sha384-ver:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) Hash.Sha384.fst

# Lax verification target for SHA-384
sha384-lax:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) --lax Hash.Sha384.fst

# Extraction target to OCaml for SHA-384
sha384-ml:
	@echo "Extracting SHA_384 to OCaml"
	mkdir -p $(SHA_ODIR)384_ml
	$(FSTAR) $(OPTIONS_OCAML) --include $(LIB_DIR) Hash.Sha384.fst --odir $(SHA_ODIR)384_ml
	cp ./lib_ml/*.ml $(SHA_ODIR)384_ml

# Verification target for SHA-512
sha512-ver:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) Hash.Sha512.fst

# Lax verification target for SHA-512
sha512-lax:
	$(FSTAR) $(OPTIONS_VER) --include $(LIB_DIR) --lax Hash.Sha512.fst

# Extraction target to OCaml for SHA-512
sha512-ml:
	@echo "Extracting SHA_512 to OCaml"
	mkdir -p $(SHA_ODIR)512_ml
	$(FSTAR) $(OPTIONS_OCAML) --include $(LIB_DIR) Hash.Sha512.fst --odir $(SHA_ODIR)512_ml
	cp ./lib_ml/*.ml $(SHA_ODIR)512_ml

# Testing target in OCaml for SHA-1
# sha1-test: sha1-ml
# 	cd $(SHA_ODIR)1_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(SHA_OCAML) Hash_Sha1.ml test_sha1.ml -o test_sha1.out
# 	$(SHA_ODIR)1_ml/test_sha1.out

# Cleanup
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(SHA_ODIR)* *~ *.exe


##
#
#   Environment
#
#

# FStar variables
FSTAR_HOME ?=/opt/fstar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

LIB_DIR=../../lib/st/
OPTIONS_VER=--universes
OPTIONS_COMPILE=--universes --lax --codegen Kremlin
OPTIONS_OCAML=--universes --lax --codegen OCaml

# OCaml variables
OCAML=ocamlfind ocamlopt -package batteries,stdint,zarith -linkpkg -g -thread

OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/ulib/ml)
OCAML_LIB=$(addprefix $(FSTAR_HOME)/ulib/ml/, MkPrims.ml Prims.ml FStar_Heap.ml FStar_Set.ml FStar_ST.ml FStar_All.ml) FStar_FunctionalExtensionality.ml FStar_Seq.ml


##
#
#   Project
#
#

# Directories
SHA_ODIR=sha
HMAC_ODIR=hmac
HKDF_ODIR=hkdf

# Files
LIB_FILES=$(addprefix $(LIB_DIR), axioms.fst intlib.fst IntLibLemmas.fst sint.fst sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SInt.UInt64.fst SInt.Cast.fst SBytes.fst)



