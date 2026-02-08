module matmul_top #(
    parameter DATA_W = 8,
    parameter ACC_W = 32,
    parameter int K = 2,
    parameter M = 2,
    parameter N = 2
)(
    input logic clk,
    input logic rst_n,
    input logic start,

    input logic signed [DATA_W-1:0] A [M][K],
    input logic signed [DATA_W-1:0] B [K][N],

    output logic signed [ACC_W-1:0] C [M][N],
    output logic done
);
    // internal signals
    logic signed [DATA_W-1:0] a_mac [M][K];
    logic signed [DATA_W-1:0] b_mac [K][N];

    logic en, clear;
    logic [$clog2(K):0] k;
    logic en_q;

    always_ff @(posedge clk) begin
        if (!rst_n)
            en_q <= 0;
        else
            en_q <= en;
    end

    // ---- Control Path module instantiation ----
    matmul_ctrlpath #(
        .K(K)
    ) ctrl0 (
        .clk(clk),
        .rst_n(rst_n),
        .start(start),
    
        .en(en), 
        .clear(clear), 
        .k(k),
        .done(done)
    );

    // ---- Data Path module instantiation ----
    matmul_datapath #(
        .DATA_W(DATA_W),
        .ACC_W(ACC_W),
        .M(M),
        .N(N),
        .K(K)
    ) datapath0 (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .clear(clear),
        .k(k),

        .A(A),
        .B(B),

        .C(C)
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

/*
matmul_core
├── matmul_ctrl.sv      ← FSM, k-counter, handshakes
├── matmul_datapath.sv  ← MAC array, accumulators
└── matmul_top.sv       ← Wires ctrl ↔ datapath

*/