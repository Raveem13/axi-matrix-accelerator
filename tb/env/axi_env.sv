class axi_env extends uvm_env;
    `uvm_component_utils(axi_env)

    axi_lite_agent axi_active;
    axi_lite_agent axi_passive;
    axi_scoreboard  scb;

    axi_stream_agent a_agent;
    axi_stream_agent b_agent;
    axi_stream_agent c_agent;
    
    axi_s_scoreboard scoreboard;

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
        
        scoreboard = axi_s_scoreboard::type_id::create("scoreboard", this);

        a_agent = axi_stream_agent::type_id::create("a_agent", this);
        b_agent = axi_stream_agent::type_id::create("b_agent", this);
        c_agent = axi_stream_agent::type_id::create("c_agent", this);

        // Configure roles
        uvm_config_db#(axis_role_e)::set(this, "a_agent.*", "role", AXIS_A);
        uvm_config_db#(axis_role_e)::set(this, "b_agent.*", "role", AXIS_B);
        uvm_config_db#(axis_role_e)::set(this, "c_agent.*", "role", AXIS_C);
        
        // // Configure activity
        uvm_config_db#(uvm_active_passive_enum)::set(this, "a_agent", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "b_agent", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "c_agent", "is_active", UVM_ACTIVE);


        uvm_config_db#(axi_s_scoreboard)::set(a_agent.monitor, "", "scoreboard", scoreboard);
        uvm_config_db#(axi_s_scoreboard)::set(b_agent.monitor, "", "scoreboard", scoreboard);
        uvm_config_db#(axi_s_scoreboard)::set(c_agent.monitor, "", "scoreboard", scoreboard);

    endfunction

    function void connect_phase(uvm_phase phase);
        axi_active.mon.ap.connect(scb.ap);
        axi_passive.mon.ap.connect(scb.ap);

        if (!a_agent.monitor) `uvm_fatal("CONNECT", "a_agent.monitor is null")
        if (!a_agent.monitor.ap) `uvm_fatal("CONNECT", "a_agent.monitor.ap is null")
        
        if (!a_agent.sequencer)
        `uvm_fatal("CONNECT", "a_agent.sequencer is NULL")

        if (!a_agent.driver)
        `uvm_fatal("CONNECT", "a_agent.driver is NULL")    
        // a_agent.monitor.ap.connect(scoreboard.ap_a);
        // b_agent.monitor.ap.connect(scoreboard.ap_b);
        // c_agent.monitor.ap.connect(scoreboard.ap_c);

        // if (a_agent.is_active == UVM_ACTIVE)
        //     a_agent.driver.seq_item_port.connect(a_agent.sequencer.seq_item_export);

        // if (b_agent.is_active == UVM_ACTIVE)
        //     b_agent.driver.seq_item_port.connect(b_agent.sequencer.seq_item_export);

        // if (c_agent.is_active == UVM_ACTIVE)
        //     c_agent.driver.seq_item_port.connect(c_agent.sequencer.seq_item_export);
    endfunction

endclass