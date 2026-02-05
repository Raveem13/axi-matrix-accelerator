module basic_tb;
  logic clk = 0;
  logic rst = 1;
  always #5 clk = ~clk;

  top dut(.clk(clk), .rst(rst));

  initial begin
    #20 rst = 0;
    #100 $finish;
  end
endmodule
