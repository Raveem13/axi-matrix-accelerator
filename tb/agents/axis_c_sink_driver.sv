class axis_c_sink_driver extends uvm_component;
  `uvm_component_utils(axis_c_sink_driver)

  virtual axi_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "No vif")
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.clk);
      if (!vif.rst_n)
        vif.m_axis_c_tready <= 0;
      else
        vif.m_axis_c_tready <= 1; // always ready sink
    end
  endtask
endclass