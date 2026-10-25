@echo off
echo REPLAY_ENTRY=PASS
setlocal EnableExtensions DisableDelayedExpansion
set "ERRORLEVEL="
set "GAMMA_MODULE="
set "GAMMA_PACKAGE_ROOT=%~dp0"
set "GAMMA_INPUT_FILE=%GAMMA_PACKAGE_ROOT%GeneratedWitness.lean"
set "GAMMA_STATUS_FILE="
set "GAMMA_FAIL_CODE=40"
set "GAMMA_FAIL_REASON=INITIALIZATION_FAILED"
set "LEAN_PATH="
set "GAMMA_EXECUTABLE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if defined GAMMA_LEAN_EXE set "GAMMA_EXECUTABLE=%GAMMA_LEAN_EXE%"
set "GAMMA_CACHE_LOCATION=%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
if defined GAMMA_CACHE_ROOT set "GAMMA_CACHE_LOCATION=%GAMMA_CACHE_ROOT%"
set "GAMMA_THREADS=2"
if defined GAMMA_LEAN_THREADS set "GAMMA_THREADS=%GAMMA_LEAN_THREADS%"
echo PACKAGE=GAMMA_TARGET622_ENDPOINT_v0_2_0
echo FIXED_TARGET=622
echo PACKAGE_ROOT="%GAMMA_PACKAGE_ROOT%"
echo INPUT_WITNESS="%GAMMA_INPUT_FILE%"
echo LEAN_EXE="%GAMMA_EXECUTABLE%"
echo CACHE_ROOT="%GAMMA_CACHE_LOCATION%"
echo STAGE=CREATE_ISOLATED_WORKSPACE
:choose_run
set "GAMMA_RUN_DIR=%GAMMA_PACKAGE_ROOT%results\replay_%RANDOM%_%RANDOM%"
if exist "%GAMMA_RUN_DIR%" goto choose_run
set "GAMMA_WORK_DIR=%GAMMA_RUN_DIR%\work"
echo OUTPUT_DIR="%GAMMA_RUN_DIR%"
echo WORK_DIR="%GAMMA_WORK_DIR%"
mkdir "%GAMMA_WORK_DIR%\GammaAdmission"
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" goto fail
if not exist "%GAMMA_WORK_DIR%\GammaAdmission\" goto fail
set "GAMMA_MAIN_LOG=%GAMMA_RUN_DIR%\replay.log"
set "GAMMA_STATUS_FILE=%GAMMA_RUN_DIR%\replay_status.txt"
> "%GAMMA_MAIN_LOG%" echo PACKAGE=GAMMA_TARGET622_ENDPOINT_v0_2_0
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" goto log_failure
> "%GAMMA_STATUS_FILE%" echo LEAN_REPLAY=PENDING
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" goto log_failure
echo REPLAY_LOG="%GAMMA_MAIN_LOG%"
>> "%GAMMA_MAIN_LOG%" echo INPUT_WITNESS="%GAMMA_INPUT_FILE%"
if not exist "%GAMMA_INPUT_FILE%" goto missing_witness
if not exist "%GAMMA_EXECUTABLE%" goto missing_lean
echo STAGE=CHECK_LEAN_VERSION
for %%F in ("%GAMMA_EXECUTABLE%") do set "PATH=%%~dpF;%PATH%"
"%GAMMA_EXECUTABLE%" --version > "%GAMMA_RUN_DIR%\lean_version.log" 2>&1
set "GAMMA_VERSION_RC=%ERRORLEVEL%"
type "%GAMMA_RUN_DIR%\lean_version.log"
type "%GAMMA_RUN_DIR%\lean_version.log" >> "%GAMMA_MAIN_LOG%"
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" goto log_failure
echo LEAN_VERSION_EXIT_CODE=%GAMMA_VERSION_RC%
if not "%GAMMA_VERSION_RC%"=="0" goto version_failure

echo STAGE=RESOLVE_OFFLINE_CACHE
if defined GAMMA_LEAN_PATH goto explicit_lean_path
if exist "%GAMMA_CACHE_LOCATION%\.lake\build\lib\lean\" set "LEAN_PATH=%GAMMA_CACHE_LOCATION%\.lake\build\lib\lean"
for /d %%D in ("%GAMMA_CACHE_LOCATION%\.lake\packages\*") do (
  set "GAMMA_DEP_DIR=%%~fD\.lake\build\lib\lean"
  call :append_dependency
)
goto dependencies_ready
:explicit_lean_path
set "LEAN_PATH=%GAMMA_LEAN_PATH%"
:dependencies_ready
if not defined LEAN_PATH goto missing_cache
set "LEAN_PATH=%GAMMA_WORK_DIR%;%LEAN_PATH%"
echo LEAN_PATH="%LEAN_PATH%"
echo LEAN_THREADS=%GAMMA_THREADS%
echo STAGE=COPY_SOURCES
copy /y "%GAMMA_PACKAGE_ROOT%GammaAdmission\*.lean" "%GAMMA_WORK_DIR%\GammaAdmission\" > "%GAMMA_RUN_DIR%\copy_modules.log" 2>&1
set "GAMMA_COPY_RC=%ERRORLEVEL%"
type "%GAMMA_RUN_DIR%\copy_modules.log"
if not "%GAMMA_COPY_RC%"=="0" goto copy_failure
copy /y "%GAMMA_INPUT_FILE%" "%GAMMA_WORK_DIR%\GeneratedWitness.lean" > "%GAMMA_RUN_DIR%\copy_witness.log" 2>&1
set "GAMMA_COPY_RC=%ERRORLEVEL%"
type "%GAMMA_RUN_DIR%\copy_witness.log"
if not "%GAMMA_COPY_RC%"=="0" goto copy_failure
if not exist "%GAMMA_WORK_DIR%\GeneratedWitness.lean" goto copy_failure
echo STAGE=COPY_ADMISSION_THEOREM
copy /y "%GAMMA_PACKAGE_ROOT%Admission622.lean" "%GAMMA_WORK_DIR%\Admission622.lean" > "%GAMMA_RUN_DIR%\copy_admission.log" 2>&1
set "GAMMA_COPY_RC=%ERRORLEVEL%"
type "%GAMMA_RUN_DIR%\copy_admission.log"
if not "%GAMMA_COPY_RC%"=="0" goto copy_failure
if not exist "%GAMMA_WORK_DIR%\Admission622.lean" goto copy_failure
echo STAGE=COPY_ENDPOINT_THEOREM
copy /y "%GAMMA_PACKAGE_ROOT%Endpoint622.lean" "%GAMMA_WORK_DIR%\Endpoint622.lean" > "%GAMMA_RUN_DIR%\copy_endpoint.log" 2>&1
set "GAMMA_COPY_RC=%ERRORLEVEL%"
type "%GAMMA_RUN_DIR%\copy_endpoint.log"
if not "%GAMMA_COPY_RC%"=="0" goto copy_failure
if not exist "%GAMMA_WORK_DIR%\Endpoint622.lean" goto copy_failure
cd /d "%GAMMA_WORK_DIR%"
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" goto directory_failure
echo STAGE=COMPILE_LEAN_MODULES
for %%F in (
  GammaAdmission\Core.lean
  GammaAdmission\GeneralEndpoint.lean
  GammaAdmission\GammaRepresentative.lean
  GammaAdmission\Coordinates.lean
  GammaAdmission\AcceleratedBinet.lean
  GammaAdmission\AcceleratedAdmission.lean
  GammaAdmission\SamplesAccelerated.lean
  GammaAdmission\MainAccelerated.lean
  GammaAdmission\RunnerReplay.lean
  GeneratedWitness.lean
  Admission622.lean
  Endpoint622.lean
) do (
  set "GAMMA_MODULE=%%F"
  call :compile_module
  if errorlevel 1 goto fail
)
> "%GAMMA_STATUS_FILE%" echo LEAN_REPLAY=PASS
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" goto log_failure
>> "%GAMMA_STATUS_FILE%" echo RESULT=FINITE_ADMISSION_AND_CONDITIONAL_ENDPOINT
>> "%GAMMA_STATUS_FILE%" echo FIXED_TARGET=622
>> "%GAMMA_STATUS_FILE%" echo FINITE_ADMISSION=PASS
>> "%GAMMA_STATUS_FILE%" echo CONDITIONAL_ENDPOINT=PASS
>> "%GAMMA_STATUS_FILE%" echo GENERIC_ENGINE_ATTACHMENT=PASS
>> "%GAMMA_STATUS_FILE%" echo REPLAY_LOG="%GAMMA_MAIN_LOG%"
>> "%GAMMA_STATUS_FILE%" echo BINET_SOUNDNESS=EXPLICIT_INPUT
>> "%GAMMA_STATUS_FILE%" echo BINET_SUCCESSOR=EXPLICIT_INPUT
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" goto log_failure
echo LEAN_REPLAY=PASS
echo FINITE_ADMISSION=PASS
echo CONDITIONAL_ENDPOINT=PASS
echo GENERIC_ENGINE_ATTACHMENT=PASS
echo REPLAY_STATUS="%GAMMA_STATUS_FILE%"
echo BINET_SOUNDNESS=EXPLICIT_INPUT
echo BINET_SUCCESSOR=EXPLICIT_INPUT
exit /b 0

:append_dependency
if not exist "%GAMMA_DEP_DIR%\" exit /b 0
if defined LEAN_PATH goto append_existing
set "LEAN_PATH=%GAMMA_DEP_DIR%"
exit /b 0
:append_existing
set "LEAN_PATH=%LEAN_PATH%;%GAMMA_DEP_DIR%"
exit /b 0

:compile_module
echo CHECK="%GAMMA_MODULE%"
set "GAMMA_FAIL_REASON=COMPILE_FAILED"
set "GAMMA_FAIL_CODE=49"
if not exist "%GAMMA_MODULE%" (
  set "GAMMA_FAIL_REASON=COMPILE_SOURCE_MISSING"
  echo COMPILE_SOURCE_MISSING="%GAMMA_MODULE%"
  exit /b 1
)
for %%F in ("%GAMMA_MODULE%") do set "GAMMA_OLEAN=%%~dpnF.olean"
for %%F in ("%GAMMA_MODULE%") do set "GAMMA_MODULE_LOG=%GAMMA_RUN_DIR%\%%~nF.log"
>> "%GAMMA_MAIN_LOG%" echo CHECK="%GAMMA_MODULE%"
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" exit /b 1
"%GAMMA_EXECUTABLE%" "-j%GAMMA_THREADS%" -o "%GAMMA_OLEAN%" "%GAMMA_MODULE%" > "%GAMMA_MODULE_LOG%" 2>&1
set "GAMMA_COMPILE_RC=%ERRORLEVEL%"
type "%GAMMA_MODULE_LOG%"
type "%GAMMA_MODULE_LOG%" >> "%GAMMA_MAIN_LOG%"
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" (
  set "GAMMA_FAIL_REASON=MODULE_LOG_APPEND_FAILED"
  exit /b 1
)
echo COMPILE_EXIT_CODE=%GAMMA_COMPILE_RC%
if not "%GAMMA_COMPILE_RC%"=="0" (
  echo COMPILE_FAIL="%GAMMA_MODULE%"
  exit /b 1
)
echo COMPILE_PASS="%GAMMA_MODULE%"
exit /b 0

:missing_witness
set "GAMMA_FAIL_REASON=WITNESS_FILE_MISSING"
goto fail
:missing_lean
set "GAMMA_FAIL_REASON=LEAN_EXECUTABLE_MISSING"
goto fail
:version_failure
set "GAMMA_FAIL_REASON=LEAN_VERSION_COMMAND_FAILED"
goto fail
:missing_cache
set "GAMMA_FAIL_REASON=OFFLINE_MATHLIB_CACHE_NOT_FOUND"
goto fail
:copy_failure
set "GAMMA_FAIL_REASON=SOURCE_COPY_FAILED"
goto fail
:directory_failure
set "GAMMA_FAIL_REASON=WORK_DIRECTORY_CHANGE_FAILED"
goto fail
:log_failure
set "GAMMA_FAIL_REASON=LOG_OR_STATUS_WRITE_FAILED"
:fail
echo LEAN_REPLAY=FAIL
echo FINITE_ADMISSION=FAIL
echo ERROR=%GAMMA_FAIL_REASON%
echo EXIT_CODE=%GAMMA_FAIL_CODE%
if not defined GAMMA_STATUS_FILE goto fail_without_status
> "%GAMMA_STATUS_FILE%" echo LEAN_REPLAY=FAIL
set "GAMMA_LAST_RC=%ERRORLEVEL%"
if not "%GAMMA_LAST_RC%"=="0" echo STATUS_WRITE=FAIL
>> "%GAMMA_STATUS_FILE%" echo FINITE_ADMISSION=FAIL
>> "%GAMMA_STATUS_FILE%" echo FIXED_TARGET=622
>> "%GAMMA_STATUS_FILE%" echo REASON=%GAMMA_FAIL_REASON%
>> "%GAMMA_STATUS_FILE%" echo MODULE="%GAMMA_MODULE%"
>> "%GAMMA_STATUS_FILE%" echo REPLAY_LOG="%GAMMA_MAIN_LOG%"
>> "%GAMMA_STATUS_FILE%" echo BINET_SOUNDNESS=EXPLICIT_INPUT
>> "%GAMMA_STATUS_FILE%" echo BINET_SUCCESSOR=EXPLICIT_INPUT
echo REPLAY_STATUS="%GAMMA_STATUS_FILE%"
:fail_without_status
echo BINET_SOUNDNESS=EXPLICIT_INPUT
echo BINET_SUCCESSOR=EXPLICIT_INPUT
exit /b %GAMMA_FAIL_CODE%
