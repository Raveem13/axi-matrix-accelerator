class axi_lite_monitor extends uvm_monitor;
    `uvm_component_utils(axi_lite_monitor)

    virtual axi_lite_if vif;
    uvm_analysis_port #(axi_lite_item) ap;
    
    bit [31:0] awaddr_q;
    bit [31:0] wdata_q;

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
        fork
            monitor_write();
            monitor_read();
        join
    endtask

    // Write monitor task
    task monitor_write();
        axi_lite_item tr;

        forever begin
            @(posedge vif.ACLK);

            // Capture Address
            if (vif.AWVALID && vif.AWREADY) begin
                awaddr_q = vif.AWADDR;
            end

            // Capture data
            if (vif.WVALID && vif.WREADY)
                wdata_q = vif.WDATA;

            // Response completes the write
            if (vif.BVALID && vif.BREADY) begin
                tr = axi_lite_item::type_id::create("wr_tr");
                tr.is_write = 1;
                tr.addr     = awaddr_q;
                tr.data     = wdata_q;
                tr.resp     = vif.BRESP;
                `uvm_info("MON",$sformatf("WRITE addr=%h data=%h resp=%0d",
                                tr.addr, tr.data, tr.resp),
                                UVM_LOW)

                ap.write(tr);
            end
        end
    endtask

    // Read monitor task
    task monitor_read();
        axi_lite_item tr;
        bit [31:0] araddr_q;

        forever begin
            @(posedge vif.ACLK);

            if (vif.ARVALID && vif.ARREADY)
                araddr_q = vif.ARADDR;

            if (vif.RVALID && vif.RREADY) begin
                tr = axi_lite_item::type_id::create("rd_tr");
                tr.is_write = 0;
                tr.addr     = araddr_q;
                tr.rdata    = vif.RDATA;
                tr.resp     = vif.RRESP;
                `uvm_info("MON",$sformatf("READ addr=%h data=%h resp=%0d",
                                                tr.addr, tr.data, tr.resp),
                                                UVM_LOW)
                ap.write(tr);
            end
        end
    endtask
endclass //axi_lite_monitor extends uvm_monitor