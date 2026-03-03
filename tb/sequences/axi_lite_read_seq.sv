class axi_lite_read_seq extends uvm_sequence #(axi_lite_item);
  `uvm_object_utils(axi_lite_read_seq)

  rand bit [31:0] addr;
  bit [31:0]      rdata;

  function new(string name="axi_lite_read_seq");
    super.new(name);
  endfunction

  task body();
    axi_lite_item rd;

    rd = axi_lite_item::type_id::create("rd");
    rd.addr  = addr;
    rd.is_write = 0;

    start_item(rd);
    finish_item(rd);

    rdata = rd.rdata;
  endtask
endclass