package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `include "tb/common/axi_types.sv"

  // Transaction first
  `include "sequence_items/axi_lite_item.sv"
  `include "sequence_items/axi_stream_packet.sv"

  // Sequences
  `include "sequences/axi_basic_seq.sv"
  `include "sequences/axi_rand_seq.sv"
  `include "sequences/axis_simple_seq.sv"
  // `include "sequences/axis_back_to_back_seq.sv"

  // Agent components
  `include "agents/axi_lite_sequencer.sv"
  `include "agents/axi_lite_driver.sv"
  `include "agents/axi_lite_monitor.sv"
  `include "agents/axi_lite_agent.sv"

  `include "tb/scoreboard/axi_s_scoreboard.sv"

  `include "agents/axi_stream_sequencer.sv"
  `include "agents/virtual_sequencer.sv"
  `include "agents/axi_stream_monitor.sv" 
  `include "agents/axi_stream_driver.sv"
  `include "agents/axi_stream_agent.sv"

  // Reference Model
  `include "tb/ref_model/axis_ref_model.sv"

  // Score board files
  `include "tb/scoreboard/axi_reg_model.sv"
  `include "tb/scoreboard/axi_scoreboard.sv"

  // Env & tests
  `include "env/axi_env.sv"
  
  `include "tests/base_test.sv"
  `include "tests/axi_rand_test.sv"
  `include "tests/axis_data_sanity_test.sv"

  // System bringup
  `include "sequences/ctrl_cfg_seq.sv"
  `include "sequences/axi_matmul_sys_vseq.sv"
  `include "env/axi_mat_accr_sys_env.sv"
  `include "tests/axi_matmul_sys_test.sv"

endpackage 