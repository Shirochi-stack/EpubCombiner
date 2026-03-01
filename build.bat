@echo off
echo ========================================
echo   Building EPUB Combiner
echo ========================================
echo.

cd /d "%~dp0"

echo Installing requirements...
pip install -r requirements.txt
echo.

echo Running PyInstaller...
pyinstaller --clean EpubCombiner.spec
echo.

set "OUT_EXE="
for %%F in ("dist\*.exe") do (
    set "OUT_EXE=%%~fF"
)

if defined OUT_EXE (
    echo ========================================
    echo   BUILD SUCCESSFUL
    echo   Output: %OUT_EXE%
    echo ========================================
) else (
    echo ========================================
    echo   BUILD FAILED - check output above
    echo ========================================
)

pause
