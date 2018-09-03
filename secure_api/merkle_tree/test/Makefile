CC ?= gcc

MERKLE_TREE_HOME = ../c
KREMLIN_HOME ?= ../../../kremlin
HACL_HOME ?= ../../..
EVERCRYPT_HOME=../../../providers/out

INCLUDE_DIRS = \
  $(MERKLE_TREE_HOME) \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib

CC_ARGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable -Wno-infinite-recursion

LD_ARGS += -L $(MERKLE_TREE_HOME) -lmerkletree
LD_ARGS += -L $(EVERCRYPT_HOME) -levercrypt
LD_ARGS += $(KREMLIN_HOME)/kremlib/out/libkremlib.a

IN_TEST_C = merkle_tree_test.c
OUT_TEST = merkle_tree_test

.PHONY: all clean

all:
	$(CC) $(CC_ARGS) $(IN_TEST_C) -o $(OUT_TEST) $(LD_ARGS)

clean:
	rm -rf $(OUT_TEST)
