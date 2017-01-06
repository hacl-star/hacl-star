Vale relies on the following tools, which must be installed before building Vale:

* Python (version 2.x), used by SCons
  * See https://www.python.org/
* SCons, the Python-based build system used by Vale
  * See http://scons.org/
* F\# (version >= 4.0), including [FsLexYacc](http://fsprojects.github.io/FsLexYacc/).  Vale is written in F\#.
  * See http://fsharp.org/ for complete information, including free versions for Windows, Mac, and Linux.
  * FsLexYacc is installed via nuget.exe; see [nuget](https://www.nuget.org/), under "latest nuget.exe"
    * In the Vale root directory, run the command "nuget.exe restore ./tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc"
    * This will create a directory tools/FsLexYacc that contains the FsLexYacc binaries; the build will expect to find these binaries in tools/FsLexYacc
* C\#, used by [Dafny](https://github.com/Microsoft/dafny/blob/master/INSTALL)
  * See https://www.visualstudio.com/vs/community/ or http://www.mono-project.com/
* An installed C compiler, used by SCons to compile C files

Once these tools are installed, running SCons in the top-level directory will build the Vale tool
and build and verify all sources in the [src](./src) directory:

python.exe scons.py
