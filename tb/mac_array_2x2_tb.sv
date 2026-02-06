module mac_array_2x2_tb;
    logic clk;
    logic rst_n;
    logic en;
    logic clear;
    logic signed [7:0] a[2][2] = '{default:0};
    logic signed [7:0] b[2][2] = '{default:0};
    logic signed [31:0] acc[2][2];

  // DUT
  mac_array_2x2 m2x2_0(
    .clk(clk),
    .rst_n(rst_n),
    .en(en),
    .clear(clear),
    .a(a),
    .b(b),
    .acc(acc)
  );

//   initial begin
//     $dumpfile("wave.vcd");
//     $dumpvars(0, basic_tb);
//   end

  // Clock
  always #5 clk = ~clk;

  initial begin
    clk = 0;
    rst_n = 0;
    en = 0;
    
    // Reset
    #20; rst_n = 1;
    clear = 0;

    // Test 1
    @(posedge clk);
    a[0][0] = 1;  b[0][0] = 2;   // 2
    a[0][1] = 3;  b[0][1] = 4;   // 12
    a[1][0] = 5;  b[1][0] = 6;   // 30
    a[1][1] = 7;  b[1][1] = 8;   // 56


    @(posedge clk);
    en = 1;

    @(posedge clk);
    // $display("Acc = %0d , Expected = 12, clear = %0d", acc, clear);
    $display("Acc = %p ", acc);

    clear = 1;
    
    en = 0;
    // Test 2
    @(posedge clk);
    clear = 0;

    a[0][0] = 2; b[0][0] = 2; // 4
    a[0][1] = 2; b[0][1] = 2; // 4
    a[1][0] = 2; b[1][0] = 2; // 4
    a[1][1] = 2; b[1][1] = 2; // 4

    @(posedge clk);
    en = 1;

    @(posedge clk);
    $display("ACC after clear = %p", acc);
    clear = 1;

    #20;
    $finish;
    
  end
endmodule
