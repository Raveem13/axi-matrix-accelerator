class axi_lite_driver extends uvm_driver #(axi_lite_item);
    `uvm_component_utils(axi_lite_driver);

    virtual axi_lite_if vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction //new()

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi_lite_if)::get(this, "","vif", vif))
            `uvm_fatal("NOVIF", "AXI Interface not set")
    endfunction

    task run_phase(uvm_phase phase);

        axi_lite_item tr;
        // Drive signals
        // `uvm_info("DRV", "Driver alive (typed)", UVM_LOW)
        `uvm_info("DRV", "Driver waiting for transaction", UVM_LOW)
        
        seq_item_port.get_next_item(tr);

        `uvm_info("DRV", $sformatf("Got txn: addr=0x%08h, data=0x%08h, is_write=%d", 
                        tr.addr, tr.wdata, tr.is_write), UVM_LOW)
        
        seq_item_port.item_done(tr);

        `uvm_info("DRV", "Transaction completed (no driving yet)", UVM_LOW)
        
    endtask
endclass //axi_lite_driver extends uvm_driver