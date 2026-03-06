class axi_matmul_sys_test extends uvm_test;
    `uvm_component_utils(axi_matmul_sys_test)

    axi_mat_accr_sys_env env;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi_mat_accr_sys_env::type_id::create("env", this);
    endfunction

    task run_phase(uvm_phase phase);
        axi_matmul_sys_vseq vseq;

        phase.raise_objection(this);

        // phase.phase_done.set_drain_time(this, 200);     // 200ns then force exit
        
        vseq = axi_matmul_sys_vseq::type_id::create("vseq");
        vseq.start(env.vseqr);

        phase.drop_objection(this);
    endtask
endclass