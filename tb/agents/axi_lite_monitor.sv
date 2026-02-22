class axi_lite_monitor extends uvm_monitor;
    `uvm_component_utils(axi_lite_monitor)

    virtual axi_lite_if vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction //new()

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(virtual axi_lite_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "AXI interface not set")
        end
    endfunction

    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        //Observations added later
    endtask
endclass //axi_lite_monitor extends uvm_monitor