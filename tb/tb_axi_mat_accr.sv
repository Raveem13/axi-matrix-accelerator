module tb_axi_mat_accr;
    localparam ADDR_W = 32;
    localparam DATA_W = 32;

    localparam START_ADDR   = 32'h00;
    localparam DONE_ADDR    = 32'h04;
    localparam CFG_M_ADDR   = 32'h08;
    localparam CFG_K_ADDR   = 32'h0C;
    localparam CFG_N_ADDR   = 32'h10;

    // -------------------------------------------------
    // Clock & Reset
    // -------------------------------------------------
    logic clk;
    logic rst_n;

    // -------------------------------------------------
    // AXI-Lite (minimal subset)
    // -------------------------------------------------
    logic        awvalid;
    logic        awready;
    logic [ADDR_W-1:0] awaddr;

    logic        wvalid;
    logic        wready;
    logic [DATA_W-1:0] wdata;

    logic        bvalid;
    logic        bresp;     
    logic        bready;

    logic        arvalid;
    logic        arready;
    logic [ADDR_W-1:0] araddr;

    logic        rvalid;
    logic        rready;
    logic [DATA_W-1:0] rdata;

    // -------------------------------------------------
    // AXI-Stream A / B / C
    // -------------------------------------------------
    logic        s_axis_a_tvalid;
    logic        s_axis_a_tready;
    logic [DATA_W-1:0] s_axis_a_tdata;
    logic        s_axis_a_tlast;

    logic        s_axis_b_tvalid;
    logic        s_axis_b_tready;
    logic [DATA_W-1:0] s_axis_b_tdata;
    logic        s_axis_b_tlast;

    logic        m_axis_c_tvalid;
    logic        m_axis_c_tready;
    logic [DATA_W-1:0] m_axis_c_tdata;
    logic        m_axis_c_tlast;

    logic        done;

    // -------------------------------------------------
    // DUT Instantiation
    // -------------------------------------------------
    axi_matrix_accelerator dut (
        .clk              (clk),
        .rst_n            (rst_n),

        // AXI-Lite
        .s_axi_awvalid    (awvalid),
        .s_axi_awready    (awready),
        .s_axi_awaddr     (awaddr),
        .s_axi_wvalid     (wvalid),
        .s_axi_bresp      (bresp),
        .s_axi_wready     (wready),
        .s_axi_wdata      (wdata),
        .s_axi_bvalid     (bvalid),
        .s_axi_bready     (bready),
        .s_axi_arvalid    (arvalid),
        .s_axi_arready    (arready),
        .s_axi_araddr     (araddr),
        .s_axi_rresp      (rresp),
        .s_axi_rvalid     (rvalid),
        .s_axi_rready     (rready),
        .s_axi_rdata      (rdata),

        // AXI-Stream
        .s_axis_a_tvalid  (s_axis_a_tvalid),
        .s_axis_a_tready  (s_axis_a_tready),
        .s_axis_a_tdata   (s_axis_a_tdata),
        .s_axis_a_tlast   (s_axis_a_tlast),

        .s_axis_b_tvalid  (s_axis_b_tvalid),
        .s_axis_b_tready  (s_axis_b_tready),
        .s_axis_b_tdata   (s_axis_b_tdata),
        .s_axis_b_tlast   (s_axis_b_tlast),

        .m_axis_c_tvalid  (m_axis_c_tvalid),
        .m_axis_c_tready  (m_axis_c_tready),
        .m_axis_c_tdata   (m_axis_c_tdata),
        .m_axis_c_tlast   (m_axis_c_tlast)

        // .done             (done)
    );


    // -------------------------------------------------
    // Clock & Reset
    // -------------------------------------------------

    initial clk = 0;
    always #5 clk = ~clk;   // 100 MHz

    // Testbench signals
    logic bp_ctrl=1, long_stall=0;

    logic [31:0] temp_data;

    // Backpressure generator for C stream
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            m_axis_c_tready    <=  1'b0;
        end 
        else if (dut.u_compute.state == dut.u_compute.OUTPUT && bp_ctrl) begin
            // Random stall
            m_axis_c_tready    <=  $urandom_range(0,1); // random backpressure
        end
        else if (long_stall) begin
            m_axis_c_tready    <=  1'b0;               // hard stall
        end
        else begin
            m_axis_c_tready    <=  1'b1;               // fully ready
        end
    end    
    // -------------------------------------------------
    // Test Sequence
    // -------------------------------------------------
    initial begin
        // Defaults
        // axi-lite_ctrl_wrapper
        awvalid = 0;
        wvalid  = 0;
        bready  = 0;

        arvalid = 0;
        rready  = 0;
        // compute_wrapper
        s_axis_a_tvalid    = 0;
        s_axis_b_tvalid    = 0;
        
        apply_reset(5);

        test_rst_mid_compute();

        test_basic_flow();
        
        test_done_readback();

        @(posedge clk);
        test_multiple_runs(3);

        #50;
        $finish;
    end

    // -------------------
    // Reset task
    // -------------------
    task apply_reset(int n_cycle);
        rst_n   =   0;
        repeat(n_cycle) @(posedge clk);
        rst_n   =   1;
        @(posedge clk);
    endtask

    // ------------------------------------
    // AXI-Lite Write Task (single beat)
    // ------------------------------------
    task axi_lite_write(
        input logic [ADDR_W-1:0] w_addr, 
        input logic [DATA_W-1:0] w_data
        );
        // Drive address & data
        awaddr  = w_addr;
        wdata   = w_data;
        awvalid = 1;
        wvalid  = 1;
        
        @(posedge clk);
        // Wait for address handshake
        wait (awready && awvalid);
        // Wait for data handshake
        wait (wready && wvalid);
        // @(posedge clk);
        
        awvalid = 0;
        wvalid = 0;

        // Wait for response
        wait (bvalid);
        $display("%t [Test] Writing data = %0d @ address = %h, BRESP = %02b",
                    $time, w_data, w_addr, bresp);

        // Complete response
        bready  = 1;
        @(posedge clk);
        bready  = 0;

    endtask //automatic

    task automatic axi_lite_read(
        input logic [ADDR_W-1:0] r_addr, 
        output logic [DATA_W-1:0] r_data
        );
        // Drive address 
        araddr  = r_addr;
        arvalid =  1;

        // Wait for handshake
        wait (arvalid && arready);
        @(posedge clk);
        // Clear valids
        arvalid =  0;

        // Wait for response
        wait (rvalid);
        r_data = rdata;
        $display("%t [Test] Reading @ address = %h, data = %0d RRESP = %02b",
                    $time, r_addr, rdata, rresp);

        // Complete response
        rready  = 1;
        @(posedge clk);
        rready  = 0;

    endtask

    task send_stream_A(
        // output logic tvalid,
        // input logic tready,
        // output logic [DATA_W-1:0] tdata,
        // output logic tlast,
        input int beats
    );
        // $display("tready = %d", s_axis_a_tready);
        wait(s_axis_a_tready);
        // $display("tready=1? = %d", s_axis_a_tready);
        for (int i=0; i<beats; ++i) begin
            @(posedge clk);
            $display("[Test] Loading beat A[%0d] = %0d", i, i);
            s_axis_a_tvalid  = 1;
            s_axis_a_tdata   = i;
            s_axis_a_tlast   = (i == beats-1);
            
        end
        @(posedge clk);
        s_axis_a_tvalid = 0;
        s_axis_a_tlast  = 0;
    endtask

    task send_stream_B(
        input int beats
    );
        wait(s_axis_b_tready);
        for (int i=0; i<beats; ++i) begin
            @(posedge clk);
            $display("[Test] Loading beat B[%0d] = %0d", i, i);
            s_axis_b_tvalid  = 1;
            s_axis_b_tdata   = i;
            s_axis_b_tlast   = (i == beats-1);
            
        end
        @(posedge clk);
        s_axis_b_tvalid = 0;
        s_axis_b_tlast  = 0;
    endtask

    task test_basic_flow();
        $display("%t -----Test Basic Flow-----", $time);
        // Defaults
        // axi-lite_ctrl_wrapper
        awvalid = 0;
        wvalid  = 0;
        bready  = 0;

        arvalid = 0;
        rready  = 0;
        // compute_wrapper
        s_axis_a_tvalid    = 0;
        s_axis_b_tvalid    = 0;
        
        $display("Setting Config & start");
        // Write config
        axi_lite_write(32'h0C, 32'd2);   // cfg_k
        axi_lite_write(32'h00, 32'h1);   // START

        // Send Matrix A then B
        $display("Starting Matrix A , B");
        fork
            send_stream_A(4);
            send_stream_B(4);
        join
        // rand_bp_test(100);

        $display("[%0t] Waiting for DONE...", $time);
        // Observe output
        wait (dut.done);
        $display("TEST PASSED: DONE asserted");
    endtask

    task test_done_readback();
        $display("%t Test1: DONE Register Readback", $time);
        @(posedge clk);     // wait a clk for done to set
        axi_lite_read(DONE_ADDR, temp_data);
        assert (temp_data[0])
            else $fatal("%t DONE register not set", $time);
    endtask

    task test_rst_mid_compute();
        axi_lite_write(CFG_K_ADDR, 2);
        axi_lite_write(START_ADDR, 1);

        fork
            send_stream_A(4);
            send_stream_B(4);
        join_none

        wait (dut.u_compute.state == dut.u_compute.COMPUTE);
        $display("%t Test2: Reset mid-transaction", $time);
        rst_n = 0;
        #20;
        rst_n = 1;
        @(posedge clk);     // wait for reset
    endtask
    
    task test_multiple_runs(int n_cycles);
        $display("%t Test4: Multiple start/done cycles (%0d cycles)", $time, n_cycles);
        repeat (n_cycles) begin
            @(posedge clk);
            test_basic_flow();
            axi_lite_write(START_ADDR, 0);
            #20;
        end
    endtask

    // Random back pressure test
    task automatic rand_bp_test(int bp_num);
        long_stall =  0;

        $display("Test3a: Random backpressure test[#random cycles = %0d]", bp_num);
        bp_ctrl =   1;
        repeat(bp_num) @(posedge clk);
        bp_ctrl =   0;
    endtask //automatic

    // Long-stall test
    task automatic long_stall_test(int s_num);
        bp_ctrl = 0;

        $display("Test3b: Long stall torture test [#stall cycles = %0d]", s_num);
        long_stall =  1;
        repeat(s_num) @(posedge clk);
        long_stall =  0;
    endtask //automatic

endmodule