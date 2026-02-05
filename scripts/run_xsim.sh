#!/usr/bin/env bash
set -e

#Test bench name
TOP=basic_tb

#Simulation snap-shot name
SIM=sim_${TOP}

#Files main path
WORK_DIR=../
cd $WORK_DIR

echo "1 ▶ Compile"
cmd.exe /c xvlog -sv -f scripts/filelist.f

echo "2 ▶ Elaborate"
cmd.exe /c xelab work.$TOP -s $SIM --debug typical

echo "3 ▶ Simulate"
cmd.exe /c xsim $SIM -runall

echo "✅Simulation Completed🔚"
