class axis_simple_seq extends uvm_sequence #(axi_stream_packet);
  `uvm_object_utils(axis_simple_seq)

  function new(string name="axis_simple_seq");
    super.new(name);
  endfunction

  task body();
    axi_stream_packet pkt;
    pkt = axi_stream_packet::type_id::create("pkt");
    // `uvm_info("AXI-SEQ", "Seq body enter", UVM_NONE)
    
    pkt.data = '{32'h1, 32'h2, 32'h3, 32'h4};
    pkt.last = 1;

    start_item(pkt);
    // `uvm_info("AXI-SEQ", "Seq body exit", UVM_NONE)
    finish_item(pkt);
  endtask
endclass