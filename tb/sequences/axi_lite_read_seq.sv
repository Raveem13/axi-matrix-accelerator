class axi_lite_read_seq extends uvm_sequence #(axi_lite_item);
  `uvm_object_utils(axi_lite_read_seq)

  bit [31:0] r_addr = 32'h0000_0004;;
  bit [31:0]      r_data;

  virtual axi_lite_if vif;

  int poll_count = 0;

  function new(string name="axi_lite_read_seq");
    super.new(name);
  endfunction

  task body();
    axi_lite_item rd;
    uvm_config_db #(virtual axi_lite_if)::get(null, "", "vif", vif);

    do begin
      `uvm_info("STATUS_SEQ", "Polling status register for completion...", UVM_LOW)
      
      rd = axi_lite_item::type_id::create("rd");
      rd.addr  = r_addr;
      rd.is_write = 0;

      start_item(rd);
      finish_item(rd);

      r_data = vif.rdata;
      $display("rdata : %h", r_data);
      poll_count++;
      if (poll_count > 500)
        `uvm_fatal("VSEQ", "Timeout waiting for status!")
    end while (r_data != 1'b1);

  endtask

endclass