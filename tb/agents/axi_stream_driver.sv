//  Class: axi_stream_driver
//
class axi_stream_driver extends uvm_driver #(axi_stream_packet);
    `uvm_component_utils(axi_stream_driver);

    virtual axi_lite_if vif;
    axis_role_e role;
    int n;

    function new(string name = "axi_stream_driver", uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual axi_lite_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "axi_if not set")
        if (!uvm_config_db#(axis_role_e)::get(this, "", "role", role))
            `uvm_fatal("NOROLE", "No role")
    endfunction
    
    task run_phase(uvm_phase phase);
        axi_stream_packet pkt;
        // `uvm_info("DRV", "Run phase", UVM_NONE)
        
        vif.a_tvalid <= 1'b0;
        vif.a_tlast  <= 1'b0;
        vif.b_tvalid <= 1'b0;
        vif.b_tlast  <= 1'b0;
        // if (role == AXIS_C) begin
        //     `uvm_info("AXIS_C", "Driving tready permanently", UVM_NONE)
        //     vif.c_tready <= 1'b1;
        //     forever @(posedge vif.clk);
        // end
        
        forever begin
            
            if (role == AXIS_C) begin
                // `uvm_info("DRV", "AXIS_C: randomizaed tready", UVM_NONE)
                @(posedge vif.clk);
                if (!vif.rst_n) begin
                    vif.c_tready <= 1'b0;
                end else begin
                    // Random c_tready test
                    vif.c_tready <= $urandom_range(0,1);
                end
                continue;
            end

            seq_item_port.get_next_item(pkt);
            // `uvm_info("DRV", "Got seq", UVM_NONE)
            $display("Packet = %p", pkt.data);
            
            for (int i = 0; i < pkt.data.size(); i++) begin
                bit done = 0;

                if (role == AXIS_A) begin
                
                vif.a_tdata  <= pkt.data[i];
                vif.a_tvalid <= 1'b1;
                vif.a_tlast  <= (i == pkt.data.size()-1);
                `uvm_info("DRV", $sformatf("A: Data=%0d", pkt.data[i]), UVM_NONE)
                end

                else if (role == AXIS_B) begin
                
                vif.b_tdata  <= pkt.data[i];
                vif.b_tvalid <= 1'b1;
                vif.b_tlast  <= (i == pkt.data.size()-1);
                `uvm_info("DRV", $sformatf("B: Data=%0d", pkt.data[i]), UVM_NONE)
                end

                // HOLD until handshake
                do begin
                    @(posedge vif.clk);
                    if (role == AXIS_A)
                    done = vif.a_tvalid && vif.a_tready;
                    else
                    done = vif.b_tvalid && vif.b_tready;
                end while (!done);

                // Deassert ONLY the active channel
                // @(posedge vif.clk);
                if (role == AXIS_A) begin
                    vif.a_tvalid <= 1'b0;
                    vif.a_tlast  <= 1'b0;
                end
                else begin
                    vif.b_tvalid <= 1'b0;
                    vif.b_tlast  <= 1'b0;
                end
                // random gap
                n = $urandom_range(0,3);
                // `uvm_info("DRV", $sformatf("%s Gap=%0d", role.name(), n), UVM_NONE)
                $display("%t %s Gap=%0d", $time, role.name(), n);
                repeat(n) @(posedge vif.clk);
            end

            seq_item_port.item_done();
        end
    endtask
    
endclass: axi_stream_driver
