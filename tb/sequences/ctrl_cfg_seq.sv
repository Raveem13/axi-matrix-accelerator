class ctrl_cfg_seq extends uvm_sequence #(axi_lite_item);
    `uvm_object_utils(ctrl_cfg_seq)

    function new(string name = "ctrl_cfg_seq");
        super.new(name);
    endfunction //new()

    virtual task body();
        axi_lite_item tr;

        `uvm_info("SEQ", "Starting AXI-Lite configuration sequence", UVM_LOW)

        tr  = axi_lite_item::type_id::create("m_tr");
        start_item(tr);
        tr.addr     =   32'h0000_0008;
        tr.wdata    =   32'h0000_0002;
        tr.is_write =   1'b1;
        finish_item(tr);

        tr  = axi_lite_item::type_id::create("k_tr");
        start_item(tr);
        tr.addr     =   32'h0000_000C;
        tr.wdata    =   32'h0000_0002;
        tr.is_write =   1'b1;
        finish_item(tr);

        tr  = axi_lite_item::type_id::create("n_tr");
        start_item(tr);
        tr.addr     =   32'h0000_0010;
        tr.wdata    =   32'h0000_0002;
        tr.is_write =   1'b1;
        finish_item(tr);

        tr  = axi_lite_item::type_id::create("s_tr");
        start_item(tr);
        tr.addr     =   32'h0000_0000;
        tr.wdata    =   32'h0000_0001;
        tr.is_write =   1'b1;
        finish_item(tr);
        // tr = axi_lite_item::type_id::create("rd_tr");
        // tr.is_write = 0;
        // tr.addr     = 32'h0000_0008;
        // start_item(tr);
        // finish_item(tr);

        `uvm_info("SEQ", "Finished AXI-Lite config sequence", UVM_LOW)
        
    endtask
endclass