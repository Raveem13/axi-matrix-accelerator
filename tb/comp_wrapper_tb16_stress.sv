module comp_wrapper_tb16_stress;
    
    localparam DATA_W   = 32;
    localparam K_MAX    = 64;

    logic   clk;
    logic   rst_n;

    // Control
    logic [15:0] cfg_k;
    logic   start;          
    logic   done;

    // AXI-Stream A
    logic [DATA_W-1:0]  a_tdata;
    logic               a_tvalid;
    logic               a_tready;
    logic               a_tlast;

    // AXI-Stream B
    logic [DATA_W-1:0]  b_tdata;
    logic               b_tvalid;
    logic               b_tready;
    logic               b_tlast;

    // AXI-Stream C
    logic [DATA_W-1:0]  c_tdata;
    logic               c_tvalid;
    logic               c_tready;
    logic               c_tlast;

    // dut instantiazion
    compute_wrapper dut (
        .clk(clk),
        .rst_n(rst_n),

        .s_axis_a_tdata(a_tdata),
        .s_axis_a_tvalid(a_tvalid),
        .s_axis_a_tready(a_tready),
        .s_axis_a_tlast(a_tlast),

        .s_axis_b_tdata(b_tdata),
        .s_axis_b_tvalid(b_tvalid),
        .s_axis_b_tready(b_tready),
        .s_axis_b_tlast(b_tlast),

        .m_axis_c_tdata(c_tdata),
        .m_axis_c_tvalid(c_tvalid),
        .m_axis_c_tready(c_tready),
        .m_axis_c_tlast(c_tlast),

        .cfg_k(cfg_k),
        .start(start),
        .done(done)
    );

    // Clock, T=10ns
    always #5 clk = ~clk;

    // C beat counter
    int c_beats;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            c_beats <= 0;
        end
        else if (c_tvalid && c_tready) begin
            c_beats <= c_beats + 1; 
        end
    end

    bit bp_ctrl, long_stall;
    // Backpressure generator for C stream
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            c_tready    <=  1'b1;
        end 
        else if (bp_ctrl) begin
            // Random stall
            c_tready    <=  $urandom_range(0,1); // random backpressure
        end
        else if (long_stall) begin
            c_tready    <=  1'b0;               // hard stall
        end
        else begin
            c_tready    <=  1'b1;               // fully ready
        end
    end        
    
    // D15 : DONE must happen exactly once per start
    int done_count;

    //Test sequence
    initial begin
        clk = 0;
        rst_n = 0;

        a_tvalid    = 0;
        a_tlast     = 0;
        b_tvalid    = 0;
        b_tlast     = 0;

        start = 0;
        cfg_k = 4;

        repeat(5) @(posedge clk);
        rst_n = 1;

        // Start computation
        @(posedge clk);
        start = 1;
        @(posedge clk);
        start = 0;

        // Send A & B streams
        send_A_B();

        rand_bp_test(10);
        long_stall_test(10);

        start_misuse_test();
        
        back_to_back_job_test();
        send_A_B();

        wait (dut.done_pulse); 
        assert (dut.done_pulse == 1);

        // Observe OUTPUT activity
        // $display("waiting for OUTPUT state"); // OUTPUT state = 6
        fork
            begin
                wait(done);
            end
            begin
                repeat (2000) @(posedge clk);
                $fatal("TIMEOUT: done never asserted");
            end
        join_any
        // wait (done);   
        $display("TB13 PASS: FSM skeleton exercised");
        
        // Final checks: beat
        if (c_beats != 8) begin
            $display("FAIL: expected 8 C beats, got %0d", c_beats);
        end else begin
            $display("PASS: 8 C beats observed");
        end
        
        @(posedge clk);
        assert (dut.done == 1);
        assert (dut.done_pulse == 0);


        // DONE must stay asserted (sticky)
        repeat (5) @(posedge clk);
        assert (dut.done == 1)
            else $fatal("done not sticky");

        // done pulse disserted (only one pulse)
        assert (dut.done_pulse == 0)
            else $fatal("no done pulse");

        // Clear DONE using direct signal (temporary TB control)
        // NOTE: Temporary TB-only hook.
        // SW clear will be verified later via AXI-Lite.
        // This is NOT architectural behavior yet.
        dut.sw_clear_done <= 1;
        @(posedge clk);
        dut.sw_clear_done <= 0;

        // DONE must clear
        @(posedge clk);
        assert (dut.done == 0)
            else $fatal("done not cleared by sw_clear");

        #20;
        $finish;
    end

    task automatic send_A_B();
        // Send A (1 beat)
        wait(a_tready);
        @(posedge clk);
        $display("Loading A");
        a_tdata     =  32'hA;
        a_tvalid    =  1'b1;
        a_tlast     =  1'b1;
        
        @(posedge clk);
        a_tvalid    = 1'b0;
        // a_tlast     = 1'b0;
        
        // Send B (1 beat)
        $display("Loading B");
        wait(b_tready);
        @(posedge clk);
        b_tdata     =  32'hB;
        b_tvalid    =  1'b1;
        b_tlast     =  1'b1;
        
        @(posedge clk);
        b_tvalid    = 1'b0;
        // b_tlast     = 1'b0;
    endtask //automatic

    // Test1: Random back pressure test
    task automatic rand_bp_test(int bp_num);
        long_stall =  0;

        $display("Test1: Random backpressure test[#random cycles = %0d]", bp_num);
        bp_ctrl =   1;
        repeat(bp_num) @(posedge clk);
        bp_ctrl =   0;
    endtask //automatic

    // Test2: Long-stall test
    task automatic long_stall_test(int s_num);
        bp_ctrl = 0;

        $display("Test2: Long stall torture test [#stall cycles = %0d]", s_num);
        long_stall =  1;
        repeat(s_num) @(posedge clk);
        long_stall =  0;
    endtask //automatic

    // Test3: Start misuse test (control-plane abuse)
    task automatic start_misuse_test();
        $display("Test3: Start misuse test");
        @(posedge clk);
        start   <=  1;
        @(posedge clk);
        start   <=  0;
    endtask //automatic

    // Test4: Back-to-back job test
    task automatic back_to_back_job_test();
        $display("Test4: Back-to-back job test"); 

        wait(done);
        dut.sw_clear_done <= 1;
        @(posedge clk);
        dut.sw_clear_done <= 0;

        start   <=  1;
        @(posedge clk);
        start   <=  0;
    endtask //automatic

endmodule