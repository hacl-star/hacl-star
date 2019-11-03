HACL_HOME = ..

all: all-tests

include ../Makefile.local

# By default, we process all the files in the current directory. Here, we
# *extend* the set of relevant files with the tests.
FSTAR_ROOTS += $(wildcard tests/*.fst) $(wildcard alternative/*.fst) $(wildcard experimental/*.fst)

# tests/Test.SHA3.fst --> tests/Test.SHA3.test
all-tests: $(patsubst %.fst,%.test,$(wildcard tests/*.fst))

%.test: %.exe
	$<

%.exe: $(ALL_CMX_FILES)
	echo "let _ = if not ($(subst .,_,$(notdir $*)).test ()) then failwith \"$* failed\";;" > \
	  $(HACL_HOME)/obj/$(notdir $*)_main.ml
	$(OCAMLOPT) $^ $(HACL_HOME)/obj/$(notdir $*)_main.ml -o $@
