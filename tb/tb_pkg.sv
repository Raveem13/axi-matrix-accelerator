package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // No Interfaces

  // AXI agent files
//   `include "axi_agent/axi_lite_item.sv"
  `include "axi_agent/axi_lite_sequencer.sv"
  `include "axi_agent/axi_lite_driver.sv"
  `include "axi_agent/axi_lite_monitor.sv"
  `include "axi_agent/axi_lite_agent.sv"

  // Env & tests
  `include "env/axi_env.sv"
  
  `include "tests/base_test.sv"

endpackage