module matmul_2x2_k2 #(
    parameter DATA_W = 8,
    parameter ACC_W = 32
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
    logic [1:0] k;
    logic signed [DATA_W-1:0] a_mac [2][2];
    logic signed [DATA_W-1:0] b_mac [2][2];

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
        WAIT,
        K0,
        K1,
        DONE
    } state_t;

    state_t state;

    // K-loop control FSM
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            state <= IDLE;
            en    <= 0;
            clear <= 0;
            done  <= 0;
            k     <= 0;
        end else begin
            case (state)

                IDLE: begin
                    en    <= 0;
                    clear <= 0;
                    done  <= 0;
                    if (start)
                        state <= CLEAR;
                end

                CLEAR: begin
                    clear <= 1;   // one clean cycle
                    en    <= 0;
                    state <= WAIT;
                end

                WAIT: begin
                    clear <= 0;
                    en    <= 0;
                    state <= K0;
                end

                K0: begin
                    clear <= 0;
                    en    <= 1;
                    k     <= 0;
                    state <= K1;
                end

                K1: begin
                    en    <= 1;
                    k     <= 1;
                    state <= DONE;
                end

                DONE: begin
                    en   <= 0;
                    done <= 1;
                end

            endcase
        end
    end

// Data mapping
    always_comb begin
        // k = 0
        if (k == 0) begin
            // $display("k=0: A = %p ", A);
            // $display("k=0: B = %p ", B);
            a_mac[0][0] = A[0][0]; b_mac[0][0] = B[0][0];
            a_mac[0][1] = A[0][0]; b_mac[0][1] = B[0][1];
            a_mac[1][0] = A[1][0]; b_mac[1][0] = B[0][0];
            a_mac[1][1] = A[1][0]; b_mac[1][1] = B[0][1];
            // $display("k=0: A_mac = %p ", a_mac);
            // $display("k=0: B_mac = %p ", b_mac);

        end 
        // k = 1
        else begin
            // $display("k=1: A = %p ", A);
            // $display("k=1: B = %p ", B);
            a_mac[0][0] = A[0][1]; b_mac[0][0] = B[1][0];
            a_mac[0][1] = A[0][1]; b_mac[0][1] = B[1][1];
            a_mac[1][0] = A[1][1]; b_mac[1][0] = B[1][0];
            a_mac[1][1] = A[1][1]; b_mac[1][1] = B[1][1];
            // $display("k=1: A_mac = %p ", a_mac);
            // $display("k=1: B_mac = %p ", b_mac);

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

    `endif

endmodule