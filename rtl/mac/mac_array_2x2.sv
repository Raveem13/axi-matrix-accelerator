module mac_array_2x2 #(
    parameter DATA_W = 8,
    parameter ACC_W = 32
)(
    input logic clk,
    input logic rst_n,
    input logic en,
    input logic clear,

    input logic signed [DATA_W-1:0]   a[2][2],
    input logic signed [DATA_W-1:0]   b[2][2],
    output logic signed [ACC_W-1:0]   acc[2][2]
);

    mac mac00(
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .clear(clear),
        .a(a[0][0]),
        .b(b[0][0]),
        .acc(acc[0][0])
    );

    mac mac01(
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .clear(clear),
        .a(a[0][1]),
        .b(b[0][1]),
        .acc(acc[0][1])
    );

    mac mac10(
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .clear(clear),
        .a(a[1][0]),
        .b(b[1][0]),
        .acc(acc[1][0])
    );

    mac mac11(
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .clear(clear),
        .a(a[1][1]),
        .b(b[1][1]),
        .acc(acc[1][1])
    );

endmodule