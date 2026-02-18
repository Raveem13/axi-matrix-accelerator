`include "uvm_macros.svh"
import uvm_pkg::*;

class axi_lite_agent extends uvm_agent;
    `uvm_component_utils(axi_lite_agent)

    axi_lite_sequencer  seqr;
    axi_lite_driver     drv;
    axi_lite_monitor    mon;


    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction //new()

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        mon = axi_lite_monitor::type_id::create("mon", this);

        if (is_active == UVM_ACTIVE) begin
            seqr    = axi_lite_sequencer::type_id::create("seqr", this);
            drv     = axi_lite_driver   ::type_id::create("drv", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        if (is_active == UVM_ACTIVE) begin
            drv.seq_item_port.connect(seqr.seq_item_export);
        end
    endfunction
endclass //axi_lite_agent extends uvm_agent