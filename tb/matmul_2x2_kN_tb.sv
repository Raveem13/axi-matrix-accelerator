module matmul_2x2_kN_tb #(
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

    logic signed [ACC_W-1:0] C_ref[2][2];
    bit mismatch;

  // DUT
  matmul_2x2_kN m2x2kN_0(
    .clk(clk),
    .rst_n(rst_n),
    .start(start),
    .A(A),
    .B(B),
    .C(C),
    .done(done)
  );

  // initial begin
  //   $dumpfile("wave_matmul_2x2_k2.vcd");
  //   $dumpvars(0, matmul_2x2_k2_tb);
  // end

  // Clock T=10ns
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
    A = '{'{1,2},'{3,4}};     // Expected C = A×B
    B = '{'{5,6},'{7,8}};     // {{19,22},{43,50}}

    // while (done == 0) begin
    //   @(posedge clk);
    // end
    // $display("Acc = %p ", C);
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
    // #20;
    // $finish;
  end

    // Checker in Scoreboard
  always @(posedge clk) begin
    if (done) begin
      golden_matmul_2x2_kn(A, B, C_ref);

      $display("----- SCOREBOARD -----");
      $display("Expected C= %p", C_ref);
      $display("DUT op : C= %p", C);

      // foreach (C_ref[i]) begin
      //     foreach (C_ref[i][j]) begin
      //         assert (!$isunknown(C_ref[i][j]))
      //             else $fatal(1,
      //                 "GOLDEN MODEL ERROR: C_ref[%0d][%0d] is X",
      //                 i, j);
      //     end
      // end

      mismatch = 0;
      for (int i=0; i<2; ++i) begin
        for (int j=0; j<2; ++j) begin
          if (C[i][j] !== C_ref[i][j]) begin
            mismatch = 1;
            $error("Mismatch at C[%0d][%0d], DUT = %0d, Exp = %0d", i, j, C[i][j], C_ref[i][j]);
          end
        end
      end
      if (mismatch) begin
        $fatal("MISMATCH: DUT result incorrect");
      end else begin
        $display("PASS: DUT result correct");
      end

      $finish;
    end
  end

endmodule

    // Reference Model
task automatic golden_matmul_2x2_kn(
  input logic signed [7:0] A [2][2],
  input logic signed [7:0] B [2][2],
  output logic signed [31:0] C_ref [2][2]
);
    
  begin
    int i, j, k;
      
    // $display("A = %p", A);
    // $display("B = %p", B);

    // Initialize
    // foreach (C_ref[i]) begin
    //   foreach (C_ref[i][j]) begin
    //     C_ref[i][j] = '0;
    //   end
    // end
    C_ref = '{default:0};

    $display("Running Ref model");
    // Maatrix Multplication
    for (i=0; i<2; ++i) begin
      for (j=0; j<2; ++j) begin
        for (k=0; k<2; ++k) begin
            C_ref[i][j] += A[i][k] * B[k][j];
        end
      end
    end
    // $display("C_ref = %p", C_ref);
  end
endtask //automatic
