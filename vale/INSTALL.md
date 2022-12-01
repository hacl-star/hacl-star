Our code relies on the following tools, which must be installed before building:

* [Python (version 3.6+)](https://www.python.org/), used by SCons
* [SCons (3.0+)](http://scons.org/), the Python-based build system used by Vale
  * On an Ubuntu system, including Windows Subsystem for Linux, you can install the Python/SCons dependencies with:
    * ```sudo apt install scons```
  * On Mac OS X (tested with El Capitan, 10.11.6), you can install the Python/SCons dependencies with:
    * ```brew install scons```
  * Note: if you run SCons under Cygwin, you might want to also install the Python `pywin32` module (via `pip`),
    which our SCons file will detect and use to stop Cygwin child processes when SCons stops
* The [Vale tool](https://github.com/project-everest/vale)
  * Download the latest [Vale binary release](https://github.com/project-everest/vale/releases) zip file
  * Set the `VALE_HOME` environment variable to the unzipped binaries directory (e.g., `VALE_HOME = vale-release-x.y.z`)
* [F*](https://github.com/FStarLang/FStar) (`master` branch),
  [KaRaMeL](https://github.com/FStarLang/karamel) (`master` branch),
  and Z3 (version [4.5.1](https://github.com/FStarLang/binaries/tree/master/z3-tested))
  * Set the `FSTAR_HOME` environment variable to the F* directory (e.g., `FSTAR_HOME = FStar`)
  * Set the `KRML_HOME` environment variable to the KaRaMeL directory (e.g., `KRML_HOME = karamel`)
  * (See the [HACL* installation guide](../INSTALL.md) for directions on installing F*, KaRaMeL, and Z3 and setting environment variables)
* An installed C/C++ compiler, used by SCons to compile C/C++ files

Once these tools are installed, running SCons in the `vale` directory will
build and verify the Vale cryptographic library:
* To build all sources in the [specs](./specs) and [code](./src) directory:
  * ```python.exe scons.py```
* To build the AES-GCM assembly language files and test executable:
  * On Windows, set the `PLATFORM` environment variable to `X64`
  * ```python.exe scons.py --FSTAR-EXTRACT obj/aesgcm.asm obj/aesgcm-gcc.S obj/aesgcm-linux.S obj/aesgcm-macos.S```
  * ```python.exe scons.py --FSTAR-EXTRACT obj/TestAesGcm.exe```
* To build in parallel, add the `-j` option (e.g., `-j 4` for 4-way parallelism).
  Any warnings about needing `pywin32` can be ignored.
* To see additional generic and Vale-specific options,
  including options to configure where to find Vale, KaRaMeL, F*, and Z3:
  * ```python.exe scons.py -h```
