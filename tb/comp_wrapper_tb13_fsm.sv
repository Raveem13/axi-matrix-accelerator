module comp_wrapper_tb13_fsm;
    
    localparam DATA_W   = 32;
    localparam K_MAX    =  2;

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

    //Test sequence
    initial begin
        clk = 0;
        rst_n = 0;

        a_tvalid    = 0;
        a_tlast     = 0;
        b_tvalid    = 0;
        b_tlast     = 0;
        c_tready    = 1;
       
        start = 0;
        cfg_k = 1;

        repeat(5) @(posedge clk);
        rst_n = 1;

        // Start computation
        @(posedge clk);
        start = 1;

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

        // Observe OUTPUT activity
        // $display("waiting for OUTPUT state");
        wait (dut.state == 3'd6);   // OUTPUT state = 6
        // repeat (10) @(posedge clk); //or wait_cycles(10);

        $display("TB13 PASS: FSM skeleton exercised");

        // Final checks: beat
        if (c_beats != 4) begin
            $display("FAIL: expected 4 C beats, got %0d", c_beats);
        end else begin
            $display("PASS: 4 C beats observed");
        end
        
        #20;
        $finish;
    end


endmodule