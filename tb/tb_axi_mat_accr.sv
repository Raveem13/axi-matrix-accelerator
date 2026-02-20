module tb_axi_mat_accr;
    localparam ADDR_W = 32;
    localparam DATA_W = 32;

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

    logic bp_ctrl=1, long_stall=0;
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
        
        $display("Setting Config & start");
        // Write config
        axi_lite_write(32'h0C, 32'd2);   // cfg_k
        axi_lite_write(32'h00, 32'h1);   // START

        // Send Matrix A then B
        $display("Starting Matrix A , B");
        fork
        //     send_stream(s_axis_a_tvalid, s_axis_a_tready,
        //                 s_axis_a_tdata, s_axis_a_tlast, 4);
            send_stream_A(4);
            send_stream_B(4);
        //     send_stream(s_axis_b_tvalid, s_axis_b_tready,
        //                 s_axis_b_tdata, s_axis_b_tlast, 4);
        join

        $display("[%0t] Waiting for DONE...", $time);
        // Observe output
        wait (dut.done);
        $display("TEST PASSED: DONE asserted");        

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
    task axi_lite_write(input logic [ADDR_W-1:0] w_addr, input logic [DATA_W-1:0] w_data);
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
  
endmodule