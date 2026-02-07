module matmul_2x2_kN #(
    parameter DATA_W = 8,
    parameter ACC_W = 32,
    parameter int K = 2,
    parameter M = 2,
    parameter N = 2
)(
    input logic clk,
    input logic rst_n,
    input logic start,

    input logic signed [DATA_W-1:0] A [2][2],
    input logic signed [DATA_W-1:0] B [2][2],

    output logic signed [ACC_W-1:0] C [2][2],
    output logic done

);
    // internal signals
    logic en, clear;
    // logic [1:0] k;
    logic signed [DATA_W-1:0] a_mac [2][2];
    logic signed [DATA_W-1:0] b_mac [2][2];
    logic [$clog2(K):0] k;

    logic en_q;

    always_ff @(posedge clk) begin
        if (!rst_n)
            en_q <= 0;
        else
            en_q <= en;
    end

    typedef enum logic [2:0] {
        IDLE,
        CLEAR,
        // WAIT,
        RUN,
        // K0,
        // K1,
        FLUSH,
        DONE
    } state_t;

    state_t state, next_state;

    always_ff @(posedge clk) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    always_comb begin
        clear = 0;
        en    = 0;
        done  = 0;
        next_state = state;

        case (state)
            IDLE:
                if (start) next_state = CLEAR;

            CLEAR: begin
                clear = 1;
                next_state = RUN;
            end

            RUN: begin
                en = 1;
                if (k_done)
                    next_state = FLUSH;
            end

            FLUSH:
                next_state = DONE;

            DONE: begin
                done = 1;
                if (!start)
                    next_state = IDLE;
            end
        endcase
    end

    always_ff @(posedge clk) begin
        if (!rst_n)
            k <= 0;
        else if (state == CLEAR)
            k <= 0;
        else if (state == RUN)
            k <= k + 1;
    end

    assign k_done = (k == K-1);

    // Data mapping
    always_comb begin
        for (int i=0; i<M; ++i) begin
            for (int j=0; j<N; ++j) begin
                a_mac[i][j] = A[i][k];
                b_mac[i][j] = B[k][j];
            end
        end
    end

    mac_array_2x2   mac_array (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .clear(clear),
        .a(a_mac),
        .b(b_mac),
        .acc(C) 
    );

    `ifndef SYNTHESIS
    // assertions here

    // k must be 0 immediately after reset deassertion
    property k_reset_check;
        @(posedge clk)
        !rst_n |=> (k == 0);
    endproperty

    assert property (k_reset_check)
        else $fatal("ASSERTION FAILED: k not reset to 0");

    // When MAC is enabled, k must be valid (0 or 1)
    property k_valid_when_en;
        @(posedge clk)
        en |-> (k inside {0,1});
    endproperty

    assert property (k_valid_when_en)
        else $fatal("ASSERTION FAILED: en asserted with invalid k=%0d", k);

    // If k=1 with en, previous en cycle must have been k=0
    property k_sequence_check;
        @(posedge clk)
        (en && k == 1) |-> $past(en && k == 0);
    endproperty

    assert property (k_sequence_check)
        else $fatal("ASSERTION FAILED: k=1 seen without prior k=0");

    // clear and en must never be high together
    property clear_en_exclusive;
        @(posedge clk)
        disable iff (!rst_n)
        !(clear && en);
    endproperty

    assert property (clear_en_exclusive)
        else $fatal("ASSERTION FAILED: clear and en asserted together");
    
    // Optional: Accumulator must only change when en=1
    property acc_changes_only_on_en;
        @(posedge clk)
        disable iff (!rst_n)
        (!en && !clear && !en_q) |-> $stable(C);
    endproperty

    assert property (acc_changes_only_on_en)
        else $fatal("ASSERTION FAILED: acc changed without en");

    property clear_zeroes_acc;
        @(posedge clk)
        clear |-> (C == '{'{0,0},'{0,0}});
    endproperty

    assert property (clear_zeroes_acc)
        else $fatal("ASSERTION FAILED: clear did not zero acc");    

    `endif

endmodule