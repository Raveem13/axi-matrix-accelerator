//  Class: axi_rand_seq
//
class axi_rand_seq extends uvm_sequence #(axi_lite_item);
    `uvm_object_utils(axi_rand_seq);

    //  Constructor: new
    function new(string name = "axi_rand_seq");
        super.new(name);
    endfunction: new

    task body();
        axi_lite_item tr;

        `uvm_info("SEQ", "Starting Random AXI-Lite sequence", UVM_LOW)

        repeat(20) begin

            tr = axi_lite_item::type_id::create("tr");
            start_item(tr);
            assert (tr.randomize());
            finish_item(tr);
        end

        `uvm_info("SEQ", "Finishing Random AXI-Lite sequence", UVM_LOW)

    endtask
    
endclass: axi_rand_seq