#!/bin/bash

	if [ x"$*" == xmozilla ]; then \
	  cp dist/Makefile.mozilla.config $(dir $@)/Makefile.config; \
	  cp dist/config.mozilla.h $(dir $@)/config.h; \
	fi
