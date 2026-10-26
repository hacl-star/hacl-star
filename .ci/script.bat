for /f "usebackq tokens=*" %%i in (`vswhere -latest -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath`) do (
  set InstallDir=%%i
)

if exist "%InstallDir%\Common7\Tools\vsdevcmd.bat" (
  "%InstallDir%\Common7\Tools\vsdevcmd.bat" -host_arch=amd64 -arch=amd64
  "%InstallDir%\Common7\Tools\vsdevcmd.bat" -test
)

cd dist/msvc-compatible
type nul > config.h
cl *.c /I ../karamel/include /I . /I ../karamel/krmllib/dist/minimal /c /DHACL_CAN_COMPILE_INTRINSICS /DHACL_CAN_COMPILE_VALE /DHACL_CAN_COMPILE_VEC128 /DHACL_CAN_COMPILE_VEC256 || goto :error
for /F %%i in ('dir /b *-x86_64-msvc.asm') do (
  ml64 /c %%i || goto :error
)
lib *.obj || goto :error
echo "SUCCESS"
exit /b 0

:error
echo "Failed"
exit /b %errorlevel%
