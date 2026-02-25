class axis_ab_monitor extends uvm_monitor;
  `uvm_component_utils(axis_ab_monitor)

  virtual axi_if vif;
  uvm_analysis_port #(axis_packet) ap;
  string stream_name;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif);
    uvm_config_db#(string)::get(this, "", "stream_name", stream_name);
  endfunction

  task run_phase(uvm_phase phase);
    forever @(posedge vif.clk);
    // no capture yet
  endtask
endclass