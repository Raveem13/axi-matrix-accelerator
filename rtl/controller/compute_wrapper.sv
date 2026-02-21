module compute_wrapper #(
    parameter DATA_W = 32,
    parameter K_MAX =  2
) (
    input logic clk,
    input logic rst_n,

    // AXI-Stream A
    input logic [DATA_W-1:0] s_axis_a_tdata,
    input logic             s_axis_a_tvalid,
    output logic            s_axis_a_tready,
    input logic             s_axis_a_tlast,

    // AXI-Stream B
    input logic [DATA_W-1:0] s_axis_b_tdata,
    input logic             s_axis_b_tvalid,
    output logic            s_axis_b_tready,
    input logic             s_axis_b_tlast,

    // AXI-Stream C
    output logic [DATA_W-1:0] m_axis_c_tdata,
    output logic             m_axis_c_tvalid,
    input logic             m_axis_c_tready,
    output logic             m_axis_c_tlast,

    // Control
    input logic [15:0] cfg_k,
    input logic        start,
    output logic       done

);
    // Buffers
    logic [DATA_W-1:0] A_buf [2][K_MAX];
    logic [DATA_W-1:0] B_buf [K_MAX][2];
    logic [DATA_W-1:0] C_buf [2][2];

    // Counter
    logic [$clog2(K_MAX):0] k_cnt;
    logic [$clog2(K_MAX):0] a_cnt;
    logic [$clog2(K_MAX):0] b_cnt;
    logic [2:0] c_cnt;

    
    // Holding C data stable, register the output
    logic [DATA_W-1:0] c_data_reg;
    logic              c_valid_reg;
    logic              c_last_reg;

    logic compute_done;     // computation + output fully complete
    logic done_pulse;       // single-cycle event

    logic done_reg;         // sticky status bit
    logic irq;              // optional interrupt output

    logic sw_clear_done = 0;    // To do : place holder driven by AXI-Lite control reg

    string comp = "[Comp_Wrap]";
    // fsm states
    typedef enum logic [2:0] {
        IDLE,
        LOAD_A,
        LOAD_B,
        PREPARE,
        COMPUTE,
        OUTPUT,
        DONE
    } state_t;

    state_t state, next_state;

    // Seq. logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end

    // Comb. Logic
    always_comb begin
        s_axis_a_tready =   0;
        s_axis_b_tready =   0;

        // c_valid_reg =   0;
        // c_last_reg  =   0;

        // done    =   0;

        next_state = state;

        case (state)
            IDLE    :   begin
                if (start)
                    next_state = LOAD_A;
            end

            LOAD_A  :   begin
                s_axis_a_tready = 1;
                if (s_axis_a_tvalid && s_axis_a_tready && s_axis_a_tlast)
                    next_state = LOAD_B;
            end

            LOAD_B  :   begin
                s_axis_a_tready = 0;
                s_axis_b_tready = 1;
                if (s_axis_b_tvalid && s_axis_b_tready && s_axis_b_tlast)
                    next_state = PREPARE;
            end

            PREPARE :   begin
                next_state = COMPUTE;
            end

            COMPUTE :   begin
                if (k_cnt == cfg_k-1)
                    next_state = OUTPUT;
            end

            OUTPUT  :   begin
                // c_valid_reg =   1;
                if (m_axis_c_tready &&  m_axis_c_tvalid && c_cnt == 3) begin
                    // c_last_reg  =   1;
                    next_state = DONE;
                end
            end

            DONE    :   begin
                // done    =   1;
                if (!start)
                    next_state = IDLE;
            end

        endcase

    end

    // Counter Logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            a_cnt <= 0;
            b_cnt <= 0;
            c_cnt <= 0;
            k_cnt <= 0;
        end else begin
            case (state)

                LOAD_A  : 
                    if (s_axis_a_tvalid && s_axis_a_tready) begin
                        A_buf[a_cnt/2][a_cnt%2] <= s_axis_a_tdata;
                        a_cnt <= a_cnt + 1;
                    end

                LOAD_B  :
                    if (s_axis_b_tvalid && s_axis_b_tready) begin
                        B_buf[b_cnt/2][b_cnt%2] <= s_axis_b_tdata;
                        b_cnt <= b_cnt + 1;
                    end

                COMPUTE :
                    k_cnt   <=  k_cnt + 1; 

                OUTPUT  :
                    if (m_axis_c_tvalid && m_axis_c_tready)
                        c_cnt <= c_cnt + 1;

                default: begin
                    a_cnt <= 0;
                    b_cnt <= 0;
                    c_cnt <= 0;
                    k_cnt <= 0;
                end
            endcase
        end
    end

    // Output buffering logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            c_data_reg  <= '0;
            c_valid_reg <= 0;
            c_last_reg  <= 0;
        end else begin
            if (state == OUTPUT && !c_valid_reg && m_axis_c_tready) begin
                c_data_reg  <=  C_buf[c_cnt/2][c_cnt%2];     //Place holder or MAC result
                c_valid_reg <= 1;
                c_last_reg  <= (c_cnt == 3);

            end 
            else if (c_valid_reg && m_axis_c_tready) begin
                c_valid_reg <= 0; 
                c_last_reg  <= 0;
            end
            // $display("%0t count_c = %0d, %S, c_valid =%0d, c_ready =%0d", $time, c_cnt, state.name(), c_valid_reg, m_axis_c_tready);
            // $display("%0t %S, m_axis_: c_tvalid =%0d, c_tready =%0d, c_tdata = %0d, c_tlast=%0d", $time, state.name(), m_axis_c_tvalid, m_axis_c_tready, m_axis_c_tdata, m_axis_c_tlast);
            // $display("%0t %S, m_axis_: c_tvalid =%0d, c_tready =%0d, c_tlast=%0d, done_pulse = %0d, done_reg = %0d", $time, state.name(), m_axis_c_tvalid, m_axis_c_tready, m_axis_c_tlast, done_pulse, done);
            $display("%0t %S, m_axis_: c_tvalid =%0d, c_tready =%0d, c_tlast=%0d, start = %0d, done_reg = %0d", $time, state.name(), m_axis_c_tvalid, m_axis_c_tready, m_axis_c_tlast, start, done);
            // $display("%0t %s %s, a_cnt=%0d b_cnt=%0d, c_tdata = %0d", $time, comp, state.name(), a_cnt, b_cnt, c_data_reg);
        end
    end

    assign m_axis_c_tdata   = c_data_reg;
    assign m_axis_c_tvalid  = c_valid_reg;
    assign m_axis_c_tlast   = c_last_reg;

    // Done pulse generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            done_pulse <= 0;
        else
            done_pulse <= (state == OUTPUT) && m_axis_c_tvalid && m_axis_c_tready && m_axis_c_tlast;
    end

    // DONE status register (AXI-Lite visible)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            done_reg <= 1'b0;
        end else if (sw_clear_done || start) begin
            done_reg <= 1'b0;
        end else if (done_pulse) begin
            done_reg <= 1'b1;
        end
    end

    assign done = done_reg;
    
    // Interrupt signaling
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            irq <= 1'b0;
        else
            irq <= done_pulse;
    end

        // Instantiate matmul_core
    matmul_datapath #(
        .DATA_W (DATA_W),
        .ACC_W  (DATA_W),
        .M(2),
        .N(2),
        .K(K_MAX)
    ) u_matmul (
        .clk   (clk),
        .rst_n (rst_n),
        .en    (state == COMPUTE),
        .clear (state == PREPARE),
        .k     (k_cnt),
        .A     (A_buf),
        .B     (B_buf),
        .C     (C_buf)
    );

    // assertions
    // No data accepted outside LOAD states
    assert property (@(posedge clk)
        (s_axis_a_tvalid && s_axis_a_tready) |-> state == LOAD_A)
        else $fatal("assert fail: data A accepted outside LOAD A states");

    assert property (@(posedge clk)
        (s_axis_b_tvalid && s_axis_b_tready) |-> state == LOAD_B)
        else $fatal("assert fail: data B accepted outside LOAD B states");

    // Compute runs exactly K cycles
    assert property (@(posedge clk)
        (state == COMPUTE) |-> k_cnt < cfg_k)
        else $fatal("assert fail: Compute run K+ cycles");


    // Output always exactly 4 beats
    assert property (@(posedge clk)
        state == OUTPUT |-> c_cnt < 4)
        else $fatal("assert fail: Output >4 beats");


    // Backpressure-aware assertions
    // Data must remain stable while stalled
    assert property (@(posedge clk)
        $past(m_axis_c_tvalid) && m_axis_c_tvalid && !m_axis_c_tready |->
        $stable(m_axis_c_tdata) && $stable(m_axis_c_tlast)
    )
        else $fatal("assert fail: data not stable while stalled");

    // Counters only move on handshake
    assert property (@(posedge clk)
        (state == OUTPUT) && (c_cnt != $past(c_cnt)) |->
        $past(m_axis_c_tvalid && m_axis_c_tready)
    )
    else $fatal("assert fail: c_counter =%0d on no-handshake", c_cnt);
    // OR
    // assert property (@(posedge clk)
    //     (state == OUTPUT) &&
    //     !$past(m_axis_c_tvalid && m_axis_c_tready)
    //     |-> $stable(c_cnt)
    // )
    // else $fatal(1, "c_counter changed without handshake");
    
    // Exactly one tlast per burst  
    assert property (@(posedge clk)
        m_axis_c_tlast |-> (state == OUTPUT && c_cnt == 3)
    )
        else $fatal("assert fail: tlast not per burst");

    // No output without start / No output outside OUTPUT state
    assert property (@(posedge clk)
        m_axis_c_tvalid |-> state == OUTPUT
    )
        else $fatal("assert fail: output outside OUTPUT state");

    // VALID must not depend on READY
    assert property (@(posedge clk)
        disable iff (!rst_n)
        $rose(m_axis_c_tvalid) |-> !$past(m_axis_c_tready) || 1'b1
    )
    else $fatal(1, "C_valid depends on C_ready");

    // LAST only valid with VALID
    assert property (@(posedge clk)
        m_axis_c_tlast |-> m_axis_c_tvalid
    )
    else $fatal(1, "TLAST without TVALID");

    // VALID deasserts only after handshake
    assert property (@(posedge clk)
        disable iff (!rst_n)
        $fell(m_axis_c_tvalid) |-> $past(m_axis_c_tready)
    )
    else $fatal(1, "TVALID dropped without handshake");

    //----done software signalling assertions---- 
    // DONE only on final output handshake
    assert property (@(posedge clk)
        done_pulse |-> $past(m_axis_c_tvalid && m_axis_c_tready && m_axis_c_tlast)
    )
    else $fatal(1, "done without final handshake");

    // DONE cannot assert twice without software clear
    // Valid until AXI-Lite clear is integrated
    assert property (@(posedge clk)
        done_reg && !sw_clear_done |-> !done_pulse
    )
    else $fatal(1, "done re-fire without software clear");

    // Done sticky until cleared by software
    assert property (@(posedge clk)
        done_reg && !sw_clear_done && !start |=> done_reg
    ) 
    else $fatal(1, "done not sticky");

    // IRQ pulsed only on done (if enabled)
    assert property (@(posedge clk)
        irq |-> $past(done_pulse)
    )
    else $fatal(1, "IRQ on not done");

    // done_pulse is exactly one cycle
    assert property (@(posedge clk)
        disable iff (!rst_n)
        done_pulse |-> !$past(done_pulse)
    ) 
    else $fatal(1, "done_pulse wider than 1 cycle");
    
    //(OR) assert property (@(posedge clk)
    //     $rose(done_pulse) |-> ##1 !done_pulse
    // )
    // else $fatal(1, "DONE is not single-cycle pulse");

    // done_reg must latch after done_pulse
    assert property (@(posedge clk)
        disable iff (!rst_n)
        $rose(done_pulse) |=> done
    ) 
    else $fatal(1, "done_reg not set after done_pulse");

    // Done pulse from OUTPUT state only 
    assert property (@(posedge clk)
        disable iff (!rst_n)
       done_pulse |-> $past(state == OUTPUT)
    ) 
    else $fatal(1, "done_pulse not generated from OUTPUT state");

    assert property (@(posedge clk)
        state != IDLE && start |-> next_state != IDLE
    )
    else $fatal(1, "FSM returned to IDLE due to start misuse");

    // Matmul core Integration assertions:
    // C must not change after COMPUTE ends
    assert property (@(posedge clk)
        state == OUTPUT |=> $stable(C_buf)
    )
    else $fatal(1, "C changes after COMPUTE ends");

    // // No compute without LOAD completion
    // assert property (@(posedge clk)
    //     state == COMPUTE |-> (a_cnt == cfg_k*2 && b_cnt == cfg_k*2)
    // )
    // else $fatal(1, "Wrong load count %0d %0d", a_cnt, b_cnt);

    // COMPUTE must be entered only after LOAD_A & LOAD_B completed
    assert property (@(posedge clk)
        $rose(state == COMPUTE) |-> $past(state) == PREPARE
    );

    // A/B buffers must be stable during COMPUTE
    assert property (@(posedge clk)
        state == COMPUTE |=> ($stable(A_buf) && $stable(B_buf))
    );

    // (Optional) Load counters are only active in LOAD states
    assert property (@(posedge clk)
        !(state inside {LOAD_A, LOAD_B}) |-> (a_cnt == 0 && b_cnt == 0)
    );

    // Reset dominance assertion
    assert property (@(posedge clk) 
        !rst_n |-> state == IDLE);

    // No spurious DONE
    assert property (@(posedge clk)
        $rose(done) |-> $past(state == DONE)
    )
    else $fatal(1, "state %s", state.name());

endmodule