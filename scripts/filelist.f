//---- rtl files ----
// mac files
rtl/top.sv
rtl/mac/mac.sv
rtl/mac/mac_array_2x2.sv
rtl/mac/matmul_2x2_k2.sv
rtl/mac/matmul_2x2_kN.sv
rtl/mac/matmul_top.sv

rtl/axi/axi_lite_ctrl_wrapper.sv

rtl/axi_matrix_accelerator.sv

// controller files
rtl/controller/controller_fsm.sv
rtl/controller/compute_wrapper.sv

rtl/mac/matmul_ctrlpath.sv
rtl/mac/matmul_datapath.sv

// ---- test-benches ----
// tb/basic_tb.sv
tb/mac_array_2x2_tb.sv
tb/matmul_2x2_k2_tb.sv
tb/matmul_2x2_kN_tb.sv
tb/matmul_core_tb.sv
tb/axi_lite_ctrl_wrapper_tb.sv
// tb/comp_wrapper_tb13_fsm.sv
// tb/comp_wrapper_tb14_backpress.sv
// tb/comp_wrapper_tb15_doneIntr.sv
tb/comp_wrapper_tb16_stress.sv

tb/tb_axi_mat_accr.sv

//-----coverage files------
tb/coverage/cov_matmul.sv