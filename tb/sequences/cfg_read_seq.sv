class cfg_read_seq extends uvm_sequence #(axi_lite_item);
    `uvm_object_utils(cfg_read_seq);

    bit [31:0] rdata;

    function new(string name = "cfg_read_seq");
        super.new(name);
    endfunction: new

    virtual task body();
        axi_lite_item tr;

        `uvm_info("SEQ", "Starting read reg Seq", UVM_LOW)

        // Read cfg_m
        tr  = axi_lite_item::type_id::create("m_tr");
        start_item(tr);
        tr.addr     =   32'h0000_0008;
        tr.is_write =   1'b0;
        finish_item(tr);
        
        // Read cfg_n
        tr  = axi_lite_item::type_id::create("k_tr");
        start_item(tr);
        tr.addr     =   32'h0000_000C;
        tr.is_write =   1'b0;
        finish_item(tr);

        // Read cfg_k
        tr  = axi_lite_item::type_id::create("n_tr");
        start_item(tr);
        tr.addr     =   32'h0000_0010;
        tr.is_write =   1'b0;
        finish_item(tr);

        // Read ctrl_start
        tr  = axi_lite_item::type_id::create("n_tr");
        start_item(tr);
        tr.addr     =   32'h0000_0000;
        tr.is_write =   1'b0;
        finish_item(tr);
        
        `uvm_info("SEQ", "Finished read reg Seq", UVM_LOW)
        
    endtask
endclass