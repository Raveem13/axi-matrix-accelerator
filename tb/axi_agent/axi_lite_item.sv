`include "uvm_macros.svh"
import uvm_pkg::*;

class axi_lite_item extends uvm_sequence_item;
    `uvm_object_utils(axi_lite_item)

    rand bit is_write;
    rand bit [31:0] addr;
    rand bit [31:0] data;

    bit [1:0] resp;
    bit [31:0] rdata;

    function new(string name="axi_lite_item");
        super.new(name);
    endfunction //new()
endclass //axi_lite_item extends uvm_sequence_item