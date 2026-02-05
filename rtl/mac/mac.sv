module mac #(
    parameter DATA_W = 8,
    parameter ACC_W = 32
)(
    input  logic clk,
    input  logic rst_n,        //active-low reset
    input  logic en,
    input  logic clear,    
    input  logic signed [DATA_W-1:0] a,
    input  logic signed [DATA_W-1:0] b,
    output logic signed [ACC_W-1:0] acc 
);

    logic signed [2*DATA_W-1:0] mul;
    logic signed [ACC_W-1:0] acc_next;

    assign mul = a * b;
    assign acc_next = acc + mul;

    always_ff @(posedge clk) begin
        if (!rst_n || clear) begin
            acc <= '0;
        end else if(en) begin
            acc <= acc_next;
        end
    end

endmodule