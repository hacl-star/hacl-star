Memcpy for instance can be verified by calling the following from code/arch/x64:

fstar.exe interop/Memcpy.fst --include ../../lib/math/ --include ../../lib/collections/ --include ../../lib/util/ --include ../ --include ../../crypto/aes/ --query_stats --smtencoding.elim_box true --include interop/ --include ../../../obj/code/crypto/poly1305/ --include ../../../obj/code/arch/x64/ --include ../../../obj/code/crypto/poly1305/x64/ --include ../../../obj/code/crypto/poly1305/ --include ../../../obj/code/arch/x64/ --include ../../../obj/code/crypto/poly1305/x64/ --include ../../../obj/code/thirdPartyPorts/OpenSSL/poly1305/x64/ --include ../../../obj/code/crypto/aes/x64/ --query_stats --include ../../../specs/defs/ --include ../../../specs/crypto/ --include ../../../specs/hardware/ --include ../../../specs/math/ --include ../../../obj/code/test/


Extraction using Kremlin can be done as follows from src/arch/x64 (on AESEncryptBE for instance)

fstar.exe interop/AESEncryptBE.fsti --include ../../lib/math/ --include ../../lib/collections/ --include ../../lib/util/ --include ../ --include ../../crypto/aes/ --query_stats --smtencoding.elim_box true --include interop/ --include ../../../obj/crypto/poly1305/ --include ../../../obj/arch/x64/ --include ../../../obj/crypto/poly1305/x64/ --include ../../../obj/crypto/poly1305/ --include ../../../obj/arch/x64/ --include ../../../obj/crypto/poly1305/x64/ --include ../../../obj/thirdPartyPorts/OpenSSL/poly1305/x64/ --include ../../../obj/crypto/aes/x64/ --query_stats --codegen Kremlin --lax --extract_module AESEncryptBE

krml -library AESEncryptBE AESEncryptBE.krml

