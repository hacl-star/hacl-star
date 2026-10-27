@echo off
setlocal
set "VSWHERE=%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe"
if not exist "%VSWHERE%" (
  echo Visual Studio Installer not found. >&2
  exit /b 1
)
set "HACL_VS_INSTALL="
for /f "usebackq delims=" %%i in (`"%VSWHERE%" -latest -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath`) do set "HACL_VS_INSTALL=%%i"
if not defined HACL_VS_INSTALL (
  echo Visual Studio with the x64 C++ tools not found. >&2
  exit /b 1
)
call "%HACL_VS_INSTALL%\Common7\Tools\VsDevCmd.bat" -host_arch=amd64 -arch=amd64 || goto :error
cd /d "%~dp0..\dist\msvc-compatible" || goto :error
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
exit /b 1
