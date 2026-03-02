class axi_matmul_sys_vseq extends uvm_sequence;
    `uvm_object_utils(axi_matmul_sys_vseq)

    virtual_sequencer vseqr;

    function new(string name = "axi_matmul_sys_vseq");
      super.new(name);
    endfunction

    task body();
      ctrl_cfg_seq   cfg_seq;
      axis_simple_seq  send_a;
      axis_simple_seq  send_b;
      axis_simple_seq  send_c;

      // Raise objection HERE
      if (starting_phase != null)
        starting_phase.raise_objection(this);

      // Cast sequencer
      if (!$cast(vseqr, m_sequencer))
        `uvm_fatal("VSEQ", "Virtual sequencer cast failed")

      // Program control plane FIRST
      cfg_seq = ctrl_cfg_seq::type_id::create("cfg_seq");
      cfg_seq.start(vseqr.ctrl_seqr);

      // Send matrix A
      send_a = axis_simple_seq::type_id::create("send_a");
      send_a.start(vseqr.a_seqr);

      // Send matrix B
      send_b = axis_simple_seq::type_id::create("send_b");
      send_b.start(vseqr.b_seqr);

      // Send C tready
      send_c = axis_simple_seq::type_id::create("send_c");
      send_c.start(vseqr.c_seqr);

      // (Optional) wait for DONE or interrupt
      // read status / poll register
      
      // Drop objection ONLY after everything is done
      if (starting_phase != null)
        starting_phase.drop_objection(this);
    endtask
endclass