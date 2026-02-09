/*
matmul_ctrl.sv      ← FSM, k-counter, handshakes

1. Control Module

matmul_ctrl.sv responsibilities ONLY:
-FSM
-k counter
-en, clear
-done

FSM:
IDLE → CLEAR → RUN (k=0..K-1) → FLUSH → DONE
*/

module matmul_ctrlpath #(
    parameter K = 2
)(
    input logic clk,
    input logic rst_n,
    input logic start,

    output logic en, 
    output logic clear, 
    output logic [$clog2(K):0] k,
    output logic done
);

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

    // k must be 0 immediately after reset deassertion
    property k_reset_check;
        @(posedge clk)
        !rst_n |=> (k == 0);
    endproperty

    assert property (k_reset_check)
        else $fatal("ASSERTION FAILED: k not reset to 0");

    // k in range
    property k_range;
        @(posedge clk) 
        en |-> (k < K);
    endproperty

    assert property (k_range)
        else $fatal("k out of range = %0d", k);    

endmodule