module matmul_2x2_k2_tb #(
    parameter DATA_W = 8,
    parameter ACC_W = 32
    );
    logic clk;
    logic rst_n;
    logic start;

    logic signed [DATA_W-1:0] A [2][2] = '{default:0};
    logic signed [DATA_W-1:0] B [2][2] = '{default:0};

    logic signed [ACC_W-1:0] C [2][2];
    logic done;

  // DUT
  matmul_2x2_k2 m2x2k2_0(
    .clk(clk),
    .rst_n(rst_n),
    .start(start),
    .A(A),
    .B(B),
    .C(C),
    .done(done)
  );

  initial begin
    $dumpfile("wave_matmul_2x2_k2.vcd");
    $dumpvars(0, matmul_2x2_k2_tb);
  end

  // Clock
  always #5 clk = ~clk;

  initial begin
    clk = 0;
    rst_n = 0;
    // en = 0;
    
    // Reset
    #20; rst_n = 1;
    @(posedge clk);
    start = 1;

    // Test 1
    // @(posedge clk);
    A = '{'{1,2},'{3,4}};
    B = '{'{5,6},'{7,8}};

    // @(posedge clk);

    // @(posedge clk);
    while (done == 0) begin
      @(posedge clk);
    end
    $display("Acc = %p ", C);
    // clear = 1;
    

    // en = 0;
    // Test 2
    // @(posedge clk);
    // clear = 0;

    // a[0][0] = 2; b[0][0] = 2; // 4
    // a[0][1] = 2; b[0][1] = 2; // 4
    // a[1][0] = 2; b[1][0] = 2; // 4
    // a[1][1] = 2; b[1][1] = 2; // 4

    // @(posedge clk);
    // en = 1;

    // @(posedge clk);
    // $display("ACC after clear = %p", acc);
    // clear = 1;

    #20;
    $finish;
    
  end
endmodule