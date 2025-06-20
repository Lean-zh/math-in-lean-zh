@echo off

call python scripts/mkall.py

if %errorlevel% neq 0 (
    echo.Error occurred in mkall.py
)

call make html

if %errorlevel% neq 0 (
    echo.Error occurred in make html
)

echo.Build process completed.
pause