SCONS=$(cygpath -d "$(dirname `which scons.bat`)/Scripts/scons.py")

PYTHON=$(cygpath -u "$(dirname `which scons.bat`)/python.exe")

"${PYTHON}" "${SCONS}" $*
