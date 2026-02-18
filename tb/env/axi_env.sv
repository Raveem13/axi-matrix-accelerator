class axi_env extends uvm_env;
    `uvm_component_utils(axi_env)

    axi_lite_agent axi_active;
    axi_lite_agent axi_passive;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        axi_active   = axi_lite_agent::type_id::create("axi_active",   this);
        axi_passive  = axi_lite_agent::type_id::create("axi_passive",  this);

        axi_active.is_active  = UVM_ACTIVE;
        axi_passive.is_active = UVM_PASSIVE;
    endfunction

endclass
