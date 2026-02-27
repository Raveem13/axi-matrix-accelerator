`include "uvm_macros.svh"
import uvm_pkg::*;

class axi_stream_sequencer extends uvm_sequencer #(axi_stream_packet);
  `uvm_component_utils(axi_stream_sequencer)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass