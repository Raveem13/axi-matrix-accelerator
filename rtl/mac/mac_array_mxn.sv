module mac_array_mxn #(
    parameter DATA_W = 8,
    parameter ACC_W = 32,
    parameter M = 2,         //matrix size
    parameter N = 2
)(
    input  logic clk,
    input  logic rst_n,        //active-low reset
    input  logic en,
    input  logic clear,
    input  logic signed [DATA_W-1:0] a [M][N],
    input  logic signed [DATA_W-1:0] b [M][N],
    output logic signed [ACC_W-1:0] acc [M][N]
);

    genvar i, j;
    generate
        for (i=0; i<M; i++) begin
            for (j=0; j<N; j++) begin
                mac #(.DATA_W(DATA_W), .ACC_W(ACC_W)) u_mac (
                    .clk(clk),
                    .rst_n(rst_n),
                    .en(en),
                    .clear(clear),
                    .a(a[i][j]),
                    .b(b[i][j]),
                    .acc(acc[i][j])
                );
            end
        end
    endgenerate

endmodule