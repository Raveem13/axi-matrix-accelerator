@echo off
echo ===============================
echo  AXI MATRIX ACCELERATOR SIM
echo ===============================

REM Go to project root
cd /d D:\GitHubProjects\Hardware\Project_1\axi_matrix_accelerator

REM -----------------------------
REM Setting Testbench top module
REM -----------------------------
set TOP=basic_tb

REM -----------------------------
REM Setting Simulation snapshot
REM -----------------------------
set SIM=sim_%TOP%

echo 1.Compile
xvlog -sv rtl\*.sv tb\*.sv
if errorlevel 1 goto :error

echo 2.Elaborate
xelab work.%TOP% -s %SIM% --debug typical
if errorlevel 1 goto :error

echo 3.Simulate
xsim %SIM% -runall
if errorlevel 1 goto :error

echo Simulation Completed 🔚
goto :eof

:error
echo ❌ Simulation Failed
exit /b 1