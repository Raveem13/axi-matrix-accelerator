class axi_stream_agent extends uvm_agent;
    `uvm_component_utils(axi_stream_agent)
    
    axi_stream_driver   driver;
    axi_strem_monitor   monitor;

    function new(string name, uvm_componet parent);
        super.new(name, parent);
    endfunction //new()

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        driver  = axi_stream_driver ::type_id::create("driver",  this);
        monitor = axi_stream_monitor::type_id::create("monitor", this);
    endfunction
    
endclass //axi_stream_agent extends uvm_agent