@echo off
setlocal
cd /d "%~dp0"
python epub_combiner.py
set EXITCODE=%ERRORLEVEL%
echo.
echo Program exited with code %EXITCODE%
echo (Close this window or press any key to exit...)
pause >nul
exit /b %EXITCODE%
