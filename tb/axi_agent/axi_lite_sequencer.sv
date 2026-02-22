`include "uvm_macros.svh"
import uvm_pkg::*;

class axi_lite_sequencer extends uvm_sequencer;
    `uvm_component_utils(axi_lite_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction //new()
endclass //axi_lite_sequencer extends uvm_sequencer