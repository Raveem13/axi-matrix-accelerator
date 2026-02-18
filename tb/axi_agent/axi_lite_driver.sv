class axi_lite_driver extends uvm_driver #(axi_lite_item);
    `uvm_component_utils(axi_lite_driver)

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
        // Drive signals
        axi_lite_item tr;

        reset_signals();

        forever begin
            seq_item_port.get_next_item(tr);

            if (tr.is_write) begin
                axi_write(tr);
            end
            else begin
                axi_read(tr);
            end

            seq_item_port.item_done();
        end

    endtask

    task reset_signals();
        vif.AWVALID <= 0;
        vif.WVALID  <= 0;
        vif.BREADY  <= 0;
        vif.ARVALID <= 0;
        vif.RREADY  <= 0;
    endtask

    // AXI-Lite write protocol
    task axi_write(axi_lite_item tr);
        // Address channel
        vif.AWADDR  <= tr.addr;
        vif.AWVALID <= 1;

        // Data channel
        vif.WADDR   <= tr.data;
        vif.WSTRB  <= 4'hF;
        vif.WVALID  <= 1;

        // Handshake independently
        fork
            begin
                @(posedge vif.ACLK);
                wait (vif.AWREADY);
                vif.AWVALID <= 0;
            end
            begin
                @(posedge vif.ACLK);
                wait (vif.WREADY);
                vif.WVALID <= 0;
            end
        join

        // Response channel
            vif.BREADY <= 1;
            @(posedge vif.ACLK);
            wait (vif.BVALID);

            tr.resp = vif.BRESP;

            vif.BREADY <= 0;

    endtask

    // AXI-Lite read protocol
    task axi_read(axi_lite_item tr);
        // Address channel
        vif.ARADDR  <= tr.addr;
        vif.ARVALID <= 1;

        // Handshake
        @(posedge vif.ACLK);
        wait (vif.ARREADY);
        vif.ARVALID <= 0;

        // Read Data channel
        vif.RREADY <= 1;
        @(posedge vif.ACLK);
        wait (vif.RVALID);

        tr.rdata= vif.RDATA;
        tr.resp = vif.RRESP;

        vif.RREADY <= 0;
    endtask

endclass //axi_lite_driver extends uvm_driver