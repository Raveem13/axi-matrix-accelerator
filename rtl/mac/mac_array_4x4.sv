module mac_array_4x4 #(
    parameter DATA_W = 8,
    parameter ACC_W = 32,
    parameter M = 4         //matrix size
)(
    input  logic clk,
    input  logic rst_n,        //active-low reset
    input  logic en,
    input  logic clear,
    input  logic signed [DATA_W-1:0] a [M][M],
    input  logic signed [DATA_W-1:0] b [M][M],
    output logic signed [ACC_W-1:0] acc [M][M]
);

    genvar i, j;
    generate
        for (i=0; i<M; i++) begin
            for (j=0; j<M; j++) begin
                mac u_mac (
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