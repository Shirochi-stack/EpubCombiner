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

if exist "dist\EpubCombiner.exe" (
    echo ========================================
    echo   BUILD SUCCESSFUL
    echo   Output: dist\EpubCombiner.exe
    echo ========================================
) else (
    echo ========================================
    echo   BUILD FAILED - check output above
    echo ========================================
)

pause
