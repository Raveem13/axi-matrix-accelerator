class axi_lite_monitor extends uvm_monitor;
    `uvm_component_utils(axi_lite_monitor)

    virtual axi_lite_if vif;

    uvm_analysis_port #(axi_lite_item) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        ap  = new("ap", this);
    endfunction //new()

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(virtual axi_lite_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "AXI interface not set")
        end
    endfunction

    task run_phase(uvm_phase phase);
        //Observations
        axi_lite_item tr;

        forever begin
            @(posedge vif.clk);

            if (vif.awvalid && vif.awready) begin
                tr  = axi_lite_item::type_id::create("tr", this);

                tr.addr     =   vif.awaddr;
                tr.is_write =   1'b1;

                // Wait for W channel
                do @(posedge vif.clk);
                while(!(vif.wvalid && vif.wready));
                
                tr.wdata    = vif.wdata; 
                tr.wstrb    = vif.wstrb; 
                
                `uvm_info("MON", $sformatf("Observed Write txn: addr=0x%08h data=0x%08h",
                                    tr.addr, tr.wdata), 
                                    UVM_LOW)
                
                ap.write(tr);    
            end

            if (vif.arvalid && vif.arready) begin
                tr  = axi_lite_item::type_id::create("tr_rd", this);

                tr.addr     =   vif.araddr;
                tr.is_write =   1'b0;

                // Wait for W channel
                do @(posedge vif.clk);
                while(!(vif.rvalid && vif.rready));
                
                tr.rdata    = vif.rdata; 
                
                `uvm_info("MON", $sformatf("Observed Read txn: addr=0x%08h data=0x%08h",
                                    tr.addr, tr.rdata), 
                                    UVM_LOW)
                
                ap.write(tr);    
            end
        end
    endtask
endclass //axi_lite_monitor extends uvm_monitor