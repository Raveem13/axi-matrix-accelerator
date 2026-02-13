module compute_wrapper #(
    parameter DATA_W = 32,
    parameter K_MAX =   2
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
    input logic     cfg_k,
    input logic     start,
    output logic    done

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

        m_axis_c_tvalid =   0;
        m_axis_c_tlast  =   0;

        done    =   0;

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
                m_axis_c_tvalid =   1;
                if (m_axis_c_tready &&  m_axis_c_tvalid && c_cnt == 3) begin
                    m_axis_c_tlast  =   1;
                    next_state = DONE;
                end
            end

            DONE    :   begin
                done    =   1;
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
                    if (s_axis_a_tvalid && s_axis_a_tready)
                        a_cnt <= a_cnt + 1;
                
                LOAD_B  :
                    if (s_axis_b_tvalid && s_axis_b_tready)
                        b_cnt <= b_cnt + 1;
                
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

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            c_data_reg  <= '0;
            c_valid_reg <= 0;
            c_last_reg  <= 0;
        end else begin
            if (state == OUTPUT && !c_valid_reg) begin
                c_data_reg  <= C_buf[0][0];     //Place holder or MAC result
                c_valid_reg <= 1;
                c_last_reg  <= (c_cnt == 3);
            end 
            else if (c_valid_reg && m_axis_c_tready) begin
                c_valid_reg <= 0; 
            end
        end
    end

    assign m_axis_c_tdata   = c_data_reg;
    assign m_axis_c_tvalid  = c_valid_reg;
    assign m_axis_c_tlast   = c_last_reg;

    // assertions
    // No data accepted outside LOAD states
    assert property (@(posedge clk)
        (s_axis_a_tvalid && s_axis_a_tready) |-> state == LOAD_A);

    assert property (@(posedge clk)
        (s_axis_b_tvalid && s_axis_b_tready) |-> state == LOAD_B);

    // Compute runs exactly K cycles
    assert property (@(posedge clk)
        (state == COMPUTE) |-> k_cnt < cfg_k);

    // Output always exactly 4 beats
    assert property (@(posedge clk)
        state == OUTPUT |-> c_cnt < 4);

    // done only asserted in DONE state
    assert property (@(posedge clk)
        done |=> state == DONE);

    // Backpressure-aware assertions
    // Data must remain stable while stalled
    assert property (@(posedge clk)
        m_axis_c_tvalid && !m_axis_c_tready |->
        $stable(m_axis_c_tdata) && $stable(m_axis_c_tlast)
    );

    // Counters only move on handshake
    assert property (@(posedge clk)
        (state == OUTPUT) && !(m_axis_c_tvalid && m_axis_c_tready) |->
        $stable(c_cnt)
    );

    // Exactly one tlast per burst
    assert property (@(posedge clk)
        m_axis_c_tlast |-> (state == OUTPUT && c_cnt == 3)
    );

    // No output without start / No output outside OUTPUT state
    assert property (@(posedge clk)
        m_axis_c_tvalid |-> state == OUTPUT
    );

endmodule