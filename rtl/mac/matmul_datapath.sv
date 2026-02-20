/*
Datapath Module

matmul_datapath.sv responsibilities ONLY:
* MAC array
* Accumulators
* A/B mapping based on `k`
*/
module matmul_datapath #(
    parameter DATA_W = 16,
    parameter ACC_W = 32,
    parameter M = 2,
    parameter N = 2,
    parameter K = 2
)(
    input logic clk,
    input logic rst_n,
    input logic en,
    input logic clear,
    input logic [$clog2(K):0] k,
    
    input logic signed [DATA_W-1:0] A [M][K],
    input logic signed [DATA_W-1:0] B [K][N],

    output logic signed [ACC_W-1:0] C [M][N]
);
    // internal signals
    logic signed [DATA_W-1:0] a_mac [2][2];
    logic signed [DATA_W-1:0] b_mac [2][2];

    logic en_q;

    string comp = "[MatMul]";

    always_ff @(posedge clk) begin
        if (!rst_n)
            en_q <= 0;
        else
            en_q <= en;
    end

    // Data mapping
    always_comb begin
        for (int i=0; i<M; ++i) begin
            for (int j=0; j<N; ++j) begin
                a_mac[i][j] = A[i][k];
                b_mac[i][j] = B[k][j];
            end
        end
        $display("%s A = %p", comp, A);
        $display("%s B = %p", comp, B);
    end

    mac_array_2x2   #(.DATA_W(DATA_W), .ACC_W(ACC_W)) mac_array (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .clear(clear),
        .a(a_mac),
        .b(b_mac),
        .acc(C) 
    );

    // Optional: Accumulator must only change when en=1
    property acc_changes_only_on_en;
        @(posedge clk)
        disable iff (!rst_n)
        (!en && !clear && !en_q) |-> $stable(C);
    endproperty

    assert property (acc_changes_only_on_en)
        else $fatal("ASSERTION FAILED: acc changed without en");

endmodule

