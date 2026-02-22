package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Transaction first
  `include "sequence_items/axi_lite_item.sv"

  // Sequences
  `include "sequences/axi_basic_seq.sv"

  // Agent components
  `include "agents/axi_lite_sequencer.sv"
  `include "agents/axi_lite_driver.sv"
  `include "agents/axi_lite_monitor.sv"
  `include "agents/axi_lite_agent.sv"

  // Env & tests
  `include "env/axi_env.sv"
  
  `include "tests/base_test.sv"

endpackage