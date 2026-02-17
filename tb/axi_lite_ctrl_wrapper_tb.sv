module axi_lite_ctrl_wrapper_tb #(
    parameter DATA_W = 32,
    parameter ADDR_W = 32
);
    logic   clk;
    logic   rst_n;
    
    // ========================
    // AXI-Lite Slave interface
    // ========================
    // ---- Write ----   
    logic [ADDR_W-1:0]  awaddr;
    logic awvalid;
    logic awready;

    logic [DATA_W-1:0]  wdata;
    logic wvalid;
    logic wready;

    logic bvalid;
    logic [1:0] bresp;
    logic bready;

        // ----Read----
    logic [ADDR_W-1:0]    araddr;
    logic       arvalid;
    logic       arready;

    logic [DATA_W-1:0]    rdata;
    logic [1:0] rresp;
    logic       rvalid;
    logic       rready;
    // ========================

    // ========================
    // Compute core interface
    logic [31:0]  cfg_m;
    logic [31:0]  cfg_k;
    logic [31:0]  cfg_n;

    logic    start;
    logic    don;
    // ========================   

    // dut instantiazion
    axi_lite_ctrl_wrapper #(
        .DATA_W(DATA_W),
        .ADDR_W(ADDR_W)
    ) dut(
        .clk(clk),
        .rst_n(rst_n),
    
        .s_axi_awaddr(awaddr),
        .s_axi_awvalid(awvalid),
        .s_axi_awready(awready),

        .s_axi_wdata(wdata),
        .s_axi_wvalid(wvalid),
        .s_axi_wready(wready),

        .s_axi_bvalid(bvalid),
        .s_axi_bresp(bresp),
        .s_axi_bready(bready),

        .s_axi_araddr(araddr),
        .s_axi_arvalid(arvalid),
        .s_axi_arready(arready),

        .s_axi_rdata(rdata),
        .s_axi_rresp(rresp),
        .s_axi_rvalid(rvalid),
        .s_axi_rready(rready),

        .cfg_m(cfg_m),
        .cfg_k(cfg_k),
        .cfg_n(cfg_n),

        .start(start),
        .done(done)
    );

    always #5 clk = ~clk;

    initial begin
        clk     = 0;
        rst_n   = 0;
        
        awvalid = 0;
        wvalid  = 0;
        bready  = 0;

        repeat(2) @(posedge clk);
        rst_n   = 1;

        write_data(32'h08, 32'd4);      // write config m
        write_data(32'h0C, 32'd5);      // write config n
        write_data(32'h10, 32'd6);      // write config k
        write_data(32'h0A, 32'd7);      // write invalid address

        // $display("BRESP : %02b", bresp);
        assert(dut.cfg_m == 32'd4);
        assert(dut.cfg_k == 32'd5);
        assert(dut.cfg_n == 32'd6);

        read_data(32'h08);              // read config m
        read_data(32'h0C);              // read config n
        read_data(32'h10);              // read config n
        read_data(32'h0A);              // write invalid address

        #40;
        $finish;
    end

    task automatic write_data(logic [ADDR_W-1:0] addr, logic [DATA_W-1:0] data);
        // Drive address & data
        awaddr  = addr;
        wdata   = data;
        awvalid = 1;
        wvalid  = 1;

        // Wait for handshake
        wait (awready && wready);
        @(posedge clk);

        // Wait for response
        wait (bvalid);
        $display("%t [Test] Writing data = %0d @ address = %h, BRESP = %02b",
                    $time, data, addr, bresp);

        // Complete response
        bready  = 1;
        @(posedge clk);
        bready  = 0;

    endtask //automatic

    task automatic read_data(logic [ADDR_W-1:0] r_addr);
        // Drive address 
        araddr  = r_addr;
        arvalid =  1;

        // Wait for handshake
        wait (arready);
        @(posedge clk);

        // Wait for response
        wait (rvalid);
        $display("%t [Test] Reading @ address = %h, data = %0d RRESP = %02b",
                    $time, r_addr, rdata, rresp);

        // Complete response
        rready  = 1;
        @(posedge clk);
        rready  = 0;

    endtask //automatic
endmodule