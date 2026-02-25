class axis_ab_driver extends uvm_driver #(axis_packet);
  `uvm_component_utils(axis_ab_driver)

  virtual axi_if vif;
  string stream_name; // "A" or "B"

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "No vif")
    uvm_config_db#(string)::get(this, "", "stream_name", stream_name);
  endfunction

  task run_phase(uvm_phase phase);
    // Day-28: idle only
    forever begin
      @(posedge vif.clk);
      if (!vif.rst_n) begin
        if (stream_name == "A") begin
          vif.s_axis_a_tvalid <= 0;
          vif.s_axis_a_tdata  <= '0;
          vif.s_axis_a_tlast  <= 0;
        end else begin
          vif.s_axis_b_tvalid <= 0;
          vif.s_axis_b_tdata  <= '0;
          vif.s_axis_b_tlast  <= 0;
        end
      end
    end
  endtask
endclass