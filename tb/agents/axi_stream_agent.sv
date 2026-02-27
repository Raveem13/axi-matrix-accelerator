class axi_stream_agent extends uvm_agent;
    `uvm_component_utils(axi_stream_agent)
    
    axi_stream_sequencer    sequencer;
    axi_stream_driver       driver;
    axi_stream_monitor      monitor;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction //new()

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
       
        monitor = axi_stream_monitor::type_id::create("monitor", this);

        if (is_active == UVM_ACTIVE) begin
            sequencer   = axi_stream_sequencer::type_id::create("sequencer", this);
            driver      = axi_stream_driver::type_id::create("driver", this);
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass //axi_stream_agent extends uvm_agent