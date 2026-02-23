package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Transaction first
  `include "sequence_items/axi_lite_item.sv"

  // Sequences
  `include "sequences/axi_basic_seq.sv"
  `include "sequences/axi_rand_seq.sv"

  // Agent components
  `include "agents/axi_lite_sequencer.sv"
  `include "agents/axi_lite_driver.sv"
  `include "agents/axi_lite_monitor.sv"
  `include "agents/axi_lite_agent.sv"

  // Score board files
  `include "tb/scoreboard/axi_reg_model.sv"
  `include "tb/scoreboard/axi_scoreboard.sv"

  // Env & tests
  `include "env/axi_env.sv"
  
  `include "tests/base_test.sv"
  `include "tests/axi_rand_test.sv"

endpackage