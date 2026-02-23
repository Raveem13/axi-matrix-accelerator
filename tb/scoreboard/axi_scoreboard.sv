//  Class: axi_scoreboard
//
class axi_scoreboard extends uvm_component;
    `uvm_component_utils(axi_scoreboard);

    //  Group: Variables
    uvm_analysis_imp #(axi_lite_item, axi_scoreboard) ap;

    axi_reg_model   ref_model;

    //  Constructor: new
    function new(string name = "axi_scoreboard", uvm_component parent);
        super.new(name, parent);
        ap  =   new("ap", this);
        ref_model = new();
    endfunction: new

    virtual function void write(axi_lite_item tr);
        
        if (tr.is_write) begin
            if (tr.resp == 2'b00) begin
                ref_model.write(tr.addr, tr.wdata);
            
                `uvm_info("SCB_WR", 
                        $sformatf("Write stored: addr=0x%08h, data=0x%08h",
                        tr.addr, tr.wdata), 
                        UVM_LOW)
            end else begin
                `uvm_info("SCB_N_WR", 
                        $sformatf("Write not stored: Invalid addr=0x%08h",
                        tr.addr), 
                        UVM_LOW)
            end
            
            
        end else begin
            bit [31:0] exp_data;
            exp_data = ref_model.read(tr.addr);

            if (exp_data !== tr.rdata) begin
                `uvm_warning("SCB", 
                            $sformatf("Read Mismatch @ addr=0x%08h, exp=0x%08h got=0x%08h", 
                                        tr.addr, exp_data, tr.rdata))
                
            end else begin
                `uvm_info("SCB", 
                $sformatf("Read Match @ addr=0x%08h, exp=0x%08h got=0x%08h", 
                                        tr.addr, exp_data, tr.rdata), 
                                        UVM_LOW)
                
            end
        end

    endfunction
    
endclass: axi_scoreboard
