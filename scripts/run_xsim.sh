#!/usr/bin/env bash
set -e

#Test bench name
# basic_tb, mac_array_2x2_tb, matmul_2x2_k2_tb, matmul_2x2_kN_tb
# CP1: matmul_core_tb
# CP2: axi_lite_ctrl_wrapper_tb
# CP3: comp_wrapper_tb13_fsm, comp_wrapper_tb14_backpress, comp_wrapper_tb15_doneIntr, comp_wrapper_tb16_stress
TOP=tb_axi_mat_accr

#Simulation snap-shot name
SIM=sim_${TOP}

#Files main path
WORK_DIR=../
cd $WORK_DIR

# cmd.exe used to run cmd in Window through WSL
echo "1 ▶ Compile"
cmd.exe /c xvlog -sv -f scripts/filelist.f

echo "2 ▶ Elaborate"
cmd.exe /c xelab work.$TOP -s $SIM --debug typical

echo "3 ▶ Simulate"
cmd.exe /c xsim $SIM -runall

echo "✅Simulation Completed🔚"
