module mac #(
    parameter A_WIDTH = 8,
    parameter B_WIDTH = 8,
    parameter ACC_WIDTH = 32
)(
    input  logic clk,
    input  logic rst_n,        //active-low reset
    input  logic en,

    input  logic signed [A_WIDTH-1:0] a,
    input  logic signed [B_WIDTH-1:0] b,
    output logic signed [ACC_WIDTH-1:0] acc 
);

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            acc <= 0;
        end else if(en)begin
            acc <= acc + (a * b);
        end
    end

endmodule