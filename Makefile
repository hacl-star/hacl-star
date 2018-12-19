# A high-level Makefile that splits out the build of HACL* in chunks.
#
# The dependency graph, encoded by hand in this Makefile, is artistically
# rendered as follows:
#
#                merkle_tree
#                |
#   secure_api   evercrypt
#            \  /  \
#            code  vale
#               \  /
#               specs

all: secure_api.build merkle_tree.build

test: providers.test specs.test merkle_tree.test

ci: all test

# ---

%.test: %.build
	$(MAKE) -C $* test

%.build:
	$(MAKE) -C $*

# ---

code.build: specs.build
vale.build: specs.build
	$(MAKE) -C vale

providers.build: code.build vale.build
secure_api.build: code.build

merkle_tree.build: providers.build
	$(MAKE) -C secure_api/merkle_tree

merkle_tree.test: merkle_tree.build
	$(MAKE) -C secure_api/merkle_tree test
