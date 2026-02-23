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
        
        forever begin
            seq_item_port.get_next_item(tr);

            if (tr.is_write) begin
                drive_write(tr);
            end else begin
                drive_read(tr);
            end
            
            seq_item_port.item_done();
        end

        `uvm_info("DRV", "Transaction completed", UVM_LOW)
        
    endtask

    task drive_write(axi_lite_item tr);

         // Address phase
        vif.awaddr  <= tr.addr;
        vif.awvalid <= 1;
        do @(posedge vif.clk);
        while (!(vif.awready));

        // Data phase
        vif.wdata  <= tr.wdata;
        vif.wvalid <= 1;

        do @(posedge vif.clk);
        while (!(vif.wready));

        vif.awvalid <= 0;
        vif.wvalid <= 0;

        // Response phase
        vif.bready <= 1;
        do @(posedge vif.clk);
        while (!vif.bvalid);
        `uvm_info("DRV_WR", $sformatf("Writing data = %0d @ address = %h, BRESP = %02b",
                            tr.wdata, tr.addr, vif.bresp), 
                            UVM_NONE)
        
        vif.bready <= 0;        
        
    endtask

    task drive_read(axi_lite_item tr);

         // Address phase
        vif.araddr  <= tr.addr;
        vif.arvalid <= 1;
        do @(posedge vif.clk);
        while (!(vif.arready));

        vif.arvalid <= 0;

        // Response phase
        vif.rready  <= 1;
        do @(posedge vif.clk);
        while (!vif.rvalid);
        `uvm_info("DRV_RD", $sformatf("Read data = %0d @ address = %h",
                            vif.rdata, tr.addr), 
                            UVM_NONE)
        
        vif.rready <= 0;       
        
    endtask

endclass //axi_lite_driver extends uvm_driver