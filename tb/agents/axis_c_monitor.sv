class axis_c_monitor extends uvm_monitor;
  `uvm_component_utils(axis_c_monitor)

  virtual axi_if vif;
  uvm_analysis_port #(axis_packet) ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif);
  endfunction

  task run_phase(uvm_phase phase);
    forever @(posedge vif.clk);
    // observe only later
  endtask
endclass