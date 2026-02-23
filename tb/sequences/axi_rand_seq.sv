//  Class: axi_rand_seq
//
class axi_rand_seq extends uvm_sequence #(axi_lite_item);
    `uvm_object_utils(axi_rand_seq);

    //  Group: Variables
        // AXI-Lite address & data
    rand bit [31:0] addr;
    rand bit [31:0] wdata;

    // Control
    rand bit    is_write; // 1 = write, 0 = read

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
    
    //  Constructor: new
    function new(string name = "axi_rand_seq");
        super.new(name);
    endfunction: new

    task body();
        axi_lite_item tr;

        `uvm_info("SEQ", "Starting Random AXI-Lite sequence", UVM_LOW)

        repeat(20) begin

            tr = axi_lite_item::type_id::create("tr");
            assert (tr.randomize() with {
                tr.is_write == is_write;
                tr.addr     == addr;
                tr.wdata    == wdata;
            }) 
            else   `uvm_error("SEQ", "Randomize fail");
            start_item(tr);
            finish_item(tr);
        end

        `uvm_info("SEQ", "Finishing Random AXI-Lite sequence", UVM_LOW)

    endtask
    
endclass: axi_rand_seq