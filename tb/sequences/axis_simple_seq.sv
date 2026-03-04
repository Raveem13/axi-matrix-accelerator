class axis_simple_seq extends uvm_sequence #(axi_stream_packet);
  `uvm_object_utils(axis_simple_seq)

  int pkt_len;

  function new(string name="axis_simple_seq");
    super.new(name);
  endfunction

  task body();
    axi_stream_packet pkt;
    int pkt_len;

    pkt = axi_stream_packet::type_id::create("pkt");
    // `uvm_info("AXI-SEQ", "Seq body enter", UVM_NONE)
    
    // pkt.data = '{32'h1, 32'h2, 32'h3, 32'h4};

    pkt.data.delete();          // If packet reused
    
    pkt_len = $urandom_range(1, 4);
    repeat (pkt_len) begin
      pkt.data.push_back($urandom_range(1,100));
    end

    pkt.last = 1;

    start_item(pkt);
    // `uvm_info("AXI-SEQ", "Seq body exit", UVM_NONE)
    finish_item(pkt);
  endtask
endclass