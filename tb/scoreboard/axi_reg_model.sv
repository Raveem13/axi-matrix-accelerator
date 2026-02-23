class axi_reg_model;
    
    bit [31:0] regfile [bit[31:0]];     // address -> data reg map

    function void write(bit [31:0] addr, bit [31:0] data);
        regfile[addr]   =   data;
    endfunction

    function bit [31:0] read (bit [31:0] addr);
        if (regfile.exists(addr)) begin
            return regfile[addr];
        end else begin
            return '0;      //default reset value
        end
    endfunction
endclass