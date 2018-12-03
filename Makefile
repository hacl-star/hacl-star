all: secure_api.build merkle_tree.build

%.build:
	$(MAKE) -C $*

code.build: specs.build

vale.build: specs.build

providers.build: code.build vale.build

secure_api.build: code.build

merkle_tree.build: providers.build
	$(MAKE) -C secure_api/merkle_tree

test:
	$(MAKE) -C providers/test

ci: all test
