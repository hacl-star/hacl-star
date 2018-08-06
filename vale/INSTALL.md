Our code relies on the following tools, which must be installed before building:

* [Python (version 3.6+)](https://www.python.org/), used by SCons
* [SCons (3.0+)](http://scons.org/), the Python-based build system used by Vale
* The [Vale tool](https://github.com/project-everest/vale)
* An installed C compiler, used by SCons to compile C files

On an Ubuntu system, including Windows Subsystem for Linux, you can install the dependencies with:
     ```sudo apt install scons```

On Mac OS X (tested with El Capitan, 10.11.6), you can install the dependencies with
    ```brew install scons```

Once these tools are installed, running SCons in the top-level directory will 
build and verify all sources in the [specs](./specs) and [code](./src) directory:

python.exe scons.py

Run with `-h` to see various generic and Vale-specific options,
including options to configure where to find Vale, KreMLin, F*, and Z3.

