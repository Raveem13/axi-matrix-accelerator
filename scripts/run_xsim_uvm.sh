#!/usr/bin/env bash
set -e

#Test bench name
# basic_tb, mac_array_2x2_tb, matmul_2x2_k2_tb, matmul_2x2_kN_tb
# CP1: matmul_core_tb
# CP2: axi_lite_ctrl_wrapper_tb
# CP3: comp_wrapper_tb13_fsm, comp_wrapper_tb14_backpress, comp_wrapper_tb15_doneIntr
TOP=tb_top

#Simulation snap-shot name
SIM=sim_${TOP}

#Files main path
WORK_DIR=../

MODE=${1:-all}   # default = all

cd $WORK_DIR

if [[ "$MODE" == "all" ]]; then
    echo "1 ▶ Compile"
    cmd.exe /c xvlog -sv -L uvm -f scripts/uvm_tb_filelist.f

    echo "2 ▶ Elaborate"
    cmd.exe /c xelab -L uvm work.$TOP -s $SIM --debug typical
fi

echo "3 ▶ Simulate"
cmd.exe /c xsim $SIM -sv_seed random -runall

echo "✅Simulation Completed🔚"
