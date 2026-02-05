module basic_tb;

  logic clk;
  logic rst_n;
  logic en;
  logic signed [7:0] a[4][4] = '{default: '0}, b[4][4] = '{default:'0};
  logic signed [31:0] acc[4][4] = '{default: '0};

  // DUT
  // mac dut (
  mac_array_4x4 #(
    .DATA_W(8),
    .ACC_W(32)
  )
  dut(
    .clk(clk),
    .rst_n(rst_n),
    .en(en),
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

    // Reset
    #20; rst_n = 1;

    // Test 1: 3*4
    @(posedge clk);
    en = 1;
    a[0][0] = 3;
    b[0][0] = 4;

    @(posedge clk);
    en = 0;

    #10;
    // $display("Acc = %0d , Expected = 12", acc);
    $display("Acc %%p = %p, Expected = 12", acc);

        // Test 2: 5*-2
    @(posedge clk);
    en = 1;
    a[0][0] = 5;
    b[0][0] = -2;

    @(posedge clk);
    en = 0;

    #10;
    // $display("Acc = %0d , Expected = 2", acc);
    $display("Acc %%p = %p, Expected = 2", acc);

    #20;
    $finish;
  end
endmodule
