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
        super.run_phase(phase);
        // Drive signals
        `uvm_info("DRV", "Driver alive (typed)", UVM_LOW)
        
    endtask
endclass //axi_lite_driver extends uvm_driver