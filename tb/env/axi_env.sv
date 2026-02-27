class axi_env extends uvm_env;
    `uvm_component_utils(axi_env)

    axi_lite_agent axi_active;
    axi_lite_agent axi_passive;
    axi_scoreboard  scb;

    axi_stream_agent a_agent;
    axi_stream_agent b_agent;
    axi_stream_agent c_agent;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        axi_active   = axi_lite_agent::type_id::create("axi_active",   this);
        axi_passive  = axi_lite_agent::type_id::create("axi_passive",  this);
        scb         = axi_scoreboard::type_id::create("scb",  this);
        
        axi_active.is_active  = UVM_PASSIVE;
        axi_passive.is_active = UVM_PASSIVE;

        a_agent = axi_stream_agent::type_id::create("a_agent", this);
        b_agent = axi_stream_agent::type_id::create("b_agent", this);
        c_agent = axi_stream_agent::type_id::create("c_agent", this);

        // Configure roles
        uvm_config_db#(axis_role_e)::set(this, "a_agent.*", "role", AXIS_A);
        uvm_config_db#(axis_role_e)::set(this, "b_agent.*", "role", AXIS_B);
        uvm_config_db#(axis_role_e)::set(this, "c_agent.*", "role", AXIS_C);
        
        // Configure activity
        uvm_config_db#(uvm_active_passive_enum)::set(this, "a_agent", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "b_agent", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "c_agent", "is_active", UVM_ACTIVE);
    endfunction

    function void connect_phase(uvm_phase phase);
        axi_active.mon.ap.connect(scb.ap);
        axi_passive.mon.ap.connect(scb.ap);
    endfunction

endclass