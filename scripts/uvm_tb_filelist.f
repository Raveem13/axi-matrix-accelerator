//---- rtl files ----
// mac files
rtl/top.sv
rtl/mac/mac.sv
rtl/mac/mac_array_2x2.sv
// rtl/mac/matmul_2x2_k2.sv
// rtl/mac/matmul_2x2_kN.sv
rtl/mac/matmul_top.sv

rtl/axi/axi_lite_ctrl_wrapper.sv

// controller files
rtl/controller/controller_fsm.sv
rtl/controller/compute_wrapper.sv

rtl/mac/matmul_ctrlpath.sv
rtl/mac/matmul_datapath.sv

// ---- test-benches ----
// tb package file
tb/tb_pkg.sv
// tb/reg/axi_regs.sv

tb/interfaces/axi_lite_if.sv
tb/sequence_items/axi_lite_item.sv

// tb/sequences/axi_base_seq.
tb/sequences/axi_basic_seq.sv
tb/sequences/axi_rand_seq.sv
// tb/sequences/start_compute_seq.sv

tb/agents/axi_lite_sequencer.sv
tb/agents/axi_lite_driver.sv
tb/agents/axi_lite_monitor.sv
tb/agents/axi_lite_agent.sv

tb/scoreboard/axi_reg_model.sv
tb/scoreboard/axi_scoreboard.sv

tb/env/axi_env.sv

tb/tests/base_test.sv
tb/tests/axi_rand_test.sv
tb/top/tb_top.sv