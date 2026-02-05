module basic_tb;

  logic clk;
  logic rst_n;
  logic en;
  logic clear;
  logic signed [7:0] a, b;
  logic signed [31:0] acc;

  // DUT
  mac dut(
    .clk(clk),
    .rst_n(rst_n),
    .en(en),
    .clear(clear),
    .a(a),
    .b(b),
    .acc(acc)
  );

  // Clock
  always #5 clk = ~clk;

  initial begin
    clk = 0;
    rst_n = 0;
    en = 0;
    a = 0;
    b = 0;

    // Reset
    #20; rst_n = 1;

    // Test 1: 3*4
    @(posedge clk);
    en = 1;
    a = 3;
    b = 4;

    @(posedge clk);
    @(posedge clk);
    en = 0;
    clear = 1;

    // #10;
    $display("Acc = %0d , Expected = 12", acc);

        // Test 2: 5*-2
    @(posedge clk);
    clear = 0;
    en = 1;
    a = 5;
    b = -2;

    @(posedge clk);
    @(posedge clk);
    en = 0;

    // #10;
    $display("Acc = %0d , Expected = 2", acc);

    #20;
    $finish;
    
  end
endmodule
