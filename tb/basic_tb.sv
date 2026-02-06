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

  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, basic_tb);
  end

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
    clear = 0;

    // Test 1: 3*4
    @(posedge clk);
    a = 3;
    b = 4;

    @(posedge clk);
    en = 1;

    @(posedge clk);
    $display("Acc = %0d , Expected = 12, clear = %0d", acc, clear);
    clear = 1;
    
    en = 0;
    // Test 2: 1*2
    @(posedge clk);
    clear = 0;

    a = 1;
    b = 2;

    @(posedge clk);
    en = 1;

    @(posedge clk);
    $display("Acc = %0d , Expected = 2, clear = %0d", acc, clear);
    clear = 1;


    #20;
    $finish;
    
  end
endmodule
