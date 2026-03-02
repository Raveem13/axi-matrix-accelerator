class axi_mat_accr_sys_env extends uvm_env;
    `uvm_component_utils(axi_mat_accr_sys_env)

    //   ctrl_env ctrl;
    //   data_env data;
    axi_env accr_sys;

    virtual_sequencer vseqr;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // ctrl  = ctrl_env ::type_id::create("ctrl", this);
        // data  = data_env ::type_id::create("data", this);
        accr_sys  = axi_env ::type_id::create("accr_sys", this);

        vseqr = virtual_sequencer::type_id::create("vseqr", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // vseqr.ctrl_seqr = ctrl.seqr;
        // vseqr.data_seqr = data.seqr;
        
        // Control plane
        vseqr.ctrl_seqr = accr_sys.axi_active.seqr;

        // Data plane
        vseqr.a_seqr = accr_sys.a_agent.sequencer;
        vseqr.b_seqr = accr_sys.b_agent.sequencer;
        vseqr.c_seqr = accr_sys.c_agent.sequencer;

        // -------------------------
        // Safety checks
        // -------------------------
        if (!vseqr.ctrl_seqr) `uvm_fatal("VSEQ", "ctrl_seqr is NULL")
        if (!vseqr.a_seqr)    `uvm_fatal("VSEQ", "a_seqr is NULL")
        if (!vseqr.b_seqr)    `uvm_fatal("VSEQ", "b_seqr is NULL")
        if (!vseqr.c_seqr)    `uvm_fatal("VSEQ", "c_seqr is NULL")
    endfunction
endclass