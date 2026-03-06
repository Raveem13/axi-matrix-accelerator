//  Class: start_ctrl_seq
class start_ctrl_seq extends uvm_sequence #(axi_lite_item);
    `uvm_object_utils(start_ctrl_seq);

    function new(string name = "start_ctrl_seq");
        super.new(name);
    endfunction: new

    virtual task body();
        axi_lite_item tr;

        `uvm_info("SEQ", "Starting Control reg Seq", UVM_LOW)

        tr  = axi_lite_item::type_id::create("s_tr");
        start_item(tr);
        tr.addr     =   32'h0000_0000;
        tr.wdata    =   32'h0000_0001;
        tr.is_write =   1'b1;
        finish_item(tr);

        `uvm_info("SEQ", "Finished Control reg Seq", UVM_LOW)
        
    endtask
endclass