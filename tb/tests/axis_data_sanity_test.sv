class axis_data_sanity_test extends uvm_test;
  `uvm_component_utils(axis_data_sanity_test)

  axi_env env;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = axi_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    axis_simple_seq seq_a;
    axis_simple_seq seq_b;

    phase.raise_objection(this);

    seq_a = axis_simple_seq::type_id::create("seq_a");
    seq_b = axis_simple_seq::type_id::create("seq_b");

    `uvm_info("SAN_Test", "Sanity test : Run phase", UVM_NONE)
    
    fork
        seq_a.start(env.a_agent.sequencer);
        seq_b.start(env.b_agent.sequencer);
    join

    #1000ns;
    phase.drop_objection(this);
  endtask
endclass