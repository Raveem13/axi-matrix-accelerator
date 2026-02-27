class axi_stream_monitor extends uvm_monitor;
    `uvm_component_utils(axi_stream_monitor)

    virtual axi_lite_if vif;

    uvm_analysis_port #(axi_stream_packet) ap;
    
    axi_stream_packet pkt;
    axis_role_e role;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        ap  = new("ap", this);
    endfunction //new()

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi_lite_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "axi_stream_if not set")
        if (!uvm_config_db#(axis_role_e)::get(this, "", "role", role))
            `uvm_fatal("NOROLE", "No role")
    endfunction

    task run_phase(uvm_phase phase);
        pkt = new();

        forever begin
            @(posedge vif.clk);
            
            case (role)
            AXIS_A : begin
                if (vif.a_tready && vif.a_tvalid) begin
                    pkt.data.push_back(vif.a_tdata);
                    
                    if (vif.a_tlast) begin
                        pkt.last = 1;
                        ap.write(pkt);

                        `uvm_info("MON_A", 
                                $sformatf("Observed A Packet, beats = %0d", pkt.data.size()), 
                                UVM_LOW)
                        pkt = new();
                    end
                end
            end
            AXIS_B : begin
                if (vif.b_tready && vif.b_tvalid) begin
                pkt.data.push_back(vif.b_tdata);
                
                    if (vif.b_tlast) begin
                        pkt.last = 1;
                        ap.write(pkt);

                        `uvm_info("MON_B", 
                                $sformatf("Observed B Packet, beats = %0d", pkt.data.size()), 
                                UVM_LOW)
                        pkt = new();
                    end
                end
            end
            AXIS_C : begin
                if (vif.c_tready && vif.c_tvalid) begin
                pkt.data.push_back(vif.c_tdata);
                
                    if (vif.c_tlast) begin
                        pkt.last = 1;
                        ap.write(pkt);

                        `uvm_info("MON_C", 
                                    $sformatf("Observed C Packet, beats = %0d, Packet data = %p", pkt.data.size(), pkt.data), 
                                    UVM_LOW)
                        pkt = new();
                    end
                end
            end
            endcase
        end
    endtask
endclass //axi_stream_monitor extends uvm_monitor