class axi_basic_seq extends uvm_sequence #(axi_lite_item);
    `uvm_object_utils(axi_basic_seq)

    function new(string name = "axi_basic_seq");
        super.new(name);
    endfunction //new()

    virtual task body();
        axi_lite_item tr;

        `uvm_info("SEQ", "Starting basic AXI-Lite sequence", UVM_LOW)

        tr  = axi_lite_item::type_id::create("tr");

        start_item(tr);
        tr.addr     =   32'h0000_0004;
        tr.wdata    =   32'hABCD_CDEF;
        tr.is_write =   1'b1;
        finish_item(tr);

        `uvm_info("SEQ", "Finished basic AXI-Lite sequence", UVM_LOW)
        
    endtask
endclass //axi_basic_seq extends uvm_seq