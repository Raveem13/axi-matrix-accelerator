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
      // wait_for_done();

    endtask

    task wait_for_done();
      axi_lite_item rd;
      bit done = 0;

      forever begin
        rd = axi_lite_item::type_id::create("rd");

        start_item(rd);
        finish_item(rd);

        done = rd.rdata[0];

        if (done) begin
          break;
        end

        #100ns;
      end
    endtask
endclass