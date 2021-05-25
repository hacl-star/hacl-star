#!/usr/bin/env bash

# Platform-independent invocation of SCons
# Inspired from the Everest script

set -e

SCONS_PYTHON_MAJOR_MINOR=3.6

# Windows-only: print out the directory of the Python associated to SCons
windows_scons_python_dir () {
    PYDIR=$(regtool -q get "/HKLM/Software/Python/PythonCore/$SCONS_PYTHON_MAJOR_MINOR/InstallPath/" || true)
    if ! [[ -d $PYDIR ]] ; then
      PYDIR=$(regtool -q get "/HKCU/Software/Python/PythonCore/$SCONS_PYTHON_MAJOR_MINOR/InstallPath/" || true)
    fi
    if ! [[ -d $PYDIR ]] ; then
      red "ERROR: Python $SCONS_PYTHON_MAJOR_MINOR was not installed properly"
      exit 1
    fi
    echo "$PYDIR"
}

is_windows () {
  [[ $OS == "Windows_NT" ]]
}

if is_windows ; then
    pydir=$(windows_scons_python_dir)
    "$pydir/python.exe" "$pydir/Scripts/scons.py" "$@"
else
    python$SCONS_PYTHON_MAJOR_MINOR $(which scons) "$@"
fi
