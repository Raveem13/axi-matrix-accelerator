//  Class: axi_stream_driver
//
class axi_stream_driver extends uvm_driver #(axi_stream_packet);
    `uvm_component_utils(axi_stream_driver);

    virtual axi_stream_if vif;

    function new(string name = "axi_stream_driver", uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual axi_stream_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "axi_stream_if not set")

    endfunction
    
    task run_phase(uvm_phase phase);
        // Drive signals
    endtask
    
endclass: axi_stream_driver
