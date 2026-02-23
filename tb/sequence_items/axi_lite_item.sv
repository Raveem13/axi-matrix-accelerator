import uvm_pkg::*;
`include "uvm_macros.svh"

class axi_lite_item extends uvm_sequence_item;

    // AXI-Lite address & data
    rand bit [31:0] addr;
    rand bit [31:0] wdata;
    bit [31:0] rdata;

    // Control
    rand bit    is_write; // 1 = write, 0 = read

    // Optional (future use)
    rand bit [3:0]  wstrb;
        bit [1:0]  resp;

    // Limit address space to valid control registers
    constraint addr_c {
        addr inside {
            32'h0000_0000,      // ctrl
            32'h0000_0004,      // status
            32'h0000_0008,      // config m
            32'h0000_000C,      // config n
            32'h0000_0010       // config k
        };
    }
    

    `uvm_object_utils_begin(axi_lite_item)
        `uvm_field_int(addr,     UVM_ALL_ON)
        `uvm_field_int(wdata,    UVM_ALL_ON)
        `uvm_field_int(rdata,    UVM_ALL_ON)
        `uvm_field_int(is_write, UVM_ALL_ON)
        `uvm_field_int(wstrb,    UVM_ALL_ON)
        `uvm_field_int(resp,     UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "axi_lite_item");
        super.new(name);
    endfunction //new()

endclass //axi_lite_item extends uvm_sequence_item