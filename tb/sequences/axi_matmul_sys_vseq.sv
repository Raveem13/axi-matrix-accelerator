class axi_matmul_sys_vseq extends uvm_sequence;
    `uvm_object_utils(axi_matmul_sys_vseq)

    virtual_sequencer vseqr;
    virtual axi_lite_if vif;

    function new(string name = "axi_matmul_sys_vseq");
      super.new(name);
    endfunction

    task body();
      ctrl_cfg_seq   cfg_seq;
      axis_simple_seq  send_a;
      axis_simple_seq  send_b;
      axis_simple_seq  send_c;

      // Raise objection HERE
      // if (starting_phase != null)
      //   starting_phase.raise_objection(this);

      // Cast sequencer
      if (!$cast(vseqr, m_sequencer))
        `uvm_fatal("VSEQ", "Virtual sequencer cast failed")

      // Program control plane FIRST
      cfg_seq = ctrl_cfg_seq::type_id::create("cfg_seq");
      cfg_seq.start(vseqr.ctrl_seqr);

      fork
        begin
          // Send matrix A
          send_a = axis_simple_seq::type_id::create("send_a");
          send_a.start(vseqr.a_seqr);
        end 

        begin
          // Send matrix B
          send_b = axis_simple_seq::type_id::create("send_b");
          send_b.start(vseqr.b_seqr);
        end
      join

      // Send C tready
      send_c = axis_simple_seq::type_id::create("send_c");
      send_c.start(vseqr.c_seqr);

      // (Optional) wait for DONE or interrupt
      // read status / poll register
      // wait_for_done();

      // Drop objection ONLY after everything is done
      // if (starting_phase != null)
      //   starting_phase.drop_objection(this);
    endtask
    
    // task wait_for_done();
    //   axi_lite_read_seq rd_seq;
    //   bit done;

    //   forever begin
    //     rd_seq = axi_lite_read_seq::type_id::create("rd_seq");
    //     rd_seq.addr = 32'h04; // STATUS reg

    //     rd_seq.start(vseqr.ctrl_seqr);

    //     done = rd_seq.rdata[0];
    //     do @(posedge vif.clk);
    //     while (done == 0);

    //     #(100ns);
    //   end
    // endtask
endclass