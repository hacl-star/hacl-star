CC ?= gcc

MERKLE_TREE_HOME = ../c
KREMLIN_HOME ?= ../../../kremlin
HACL_HOME ?= ../../..
EVERCRYPT_HOME=../../../providers/out
EVERCRYPT_INCLUDE=../../../providers/generated

INCLUDE_DIRS = \
  $(MERKLE_TREE_HOME) \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
	$(EVERCRYPT_INCLUDE)

CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable -Wno-infinite-recursion

LD_ARGS += $(MERKLE_TREE_HOME)/libmerkletree.a

# Do not use below: if used, the loader tries to use "libevercrypt.so" and gives an error.
# LD_ARGS += -L $(EVERCRYPT_HOME) -levercrypt
LD_ARGS += $(EVERCRYPT_HOME)/libevercrypt.a

LD_ARGS += $(KREMLIN_HOME)/kremlib/out/libkremlib.a

IN_TEST_C = merkle_tree_test.c
OUT_TEST = merkle_tree_test

.PHONY: all clean

all:
	make -C ../
	$(CC) $(CFLAGS) $(IN_TEST_C) -o $(OUT_TEST) $(LD_ARGS)

test-asan: all
	clang -O1 -g -fsanitize=address -fno-omit-frame-pointer $(CFLAGS) $(IN_TEST_C) -o $(OUT_TEST).asan $(LD_ARGS)

clean:
	rm -rf $(OUT_TEST) $(OUT_TEST).asan
