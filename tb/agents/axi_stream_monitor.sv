class axi_stream_monitor extends uvm_monitor;
    `uvm_object_utils(axi_stream_monitor)

    virtual axi_stream_if vif;

    uvm_analysis_port #(axi_stream_packet) ap;
    
    axi_stream_packet curr_pkt;
    
    function new(string name, uvm_parent parent);
        super.new(name, parent);
        ap  = new("ap", this);
    endfunction //new()

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi_stream_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "axi_stream_if not set")
    endfunction

    task tun_phase(uvm_phase phase);
        curr_pkt    =   null;
        
        forever begin
            @(posedge vif.ACLK);

            if (!vif.ARST_N) begin
                curr_pkt = null;
                continue;
            end
            if (vif.TVALID && vif.TREADY) begin
                if (curr_pkt == null) begin
                    curr_pkt = axi_stream_packet::type_id::create("curr_pkt");
                end
                curr_pkt.data.push_back(vif.TDATA);
            end
            if (vif.TLAST) begin
                ap.write(curr_pkt);
                curr_pkt   = null;
            end
        end
    endtask
endclass //axi_stream_monitor extends uvm_monitor