module mac_array_4x4 #(
    parameter A_WIDTH = 8,
    parameter B_WIDTH = 8,
    parameter ACC_WIDTH = 32,
    parameter M = 4         //matrix size
)(
    input  logic clk,
    input  logic rst_n,        //active-low reset
    input  logic en,

    input  logic signed [A_WIDTH-1:0] a [M][M],
    input  logic signed [B_WIDTH-1:0] b [M][M],
    output logic signed [ACC_WIDTH-1:0] acc [M][M]
);

    genvar i, j;
    generate
        for (i=0; i<M; ++i) begin
            for (j=0; j<M; ++j) begin
                mac u_mac (
                    .clk(clk),
                    .rst_n(rst_n),
                    .en(en),
                    .a(a[i][j]),
                    .b(b[i][j]),
                    .acc(acc[i][j])
                );
            end
        end
    endgenerate

endmodule