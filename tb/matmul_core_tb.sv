module matmul_core_tb #(
    parameter DATA_W = 16,
    parameter ACC_W = 32,
    parameter K = 5,
    parameter M = 2,
    parameter N = 2
    );

    logic clk;
    logic rst_n;
    logic start;

    logic signed [DATA_W-1:0] A [2][K] = '{default:0};
    logic signed [DATA_W-1:0] B [K][2] = '{default:0};

    logic signed [ACC_W-1:0] C [2][2];
    logic done;

    logic signed [ACC_W-1:0] C_ref[2][2];
    bit mismatch;

  // DUT
  matmul_top m2x2kN_0(
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
    A = '{'{1,2,2,2,2},'{3,4,4,4,4}};     // Expected C = A×B
    B = '{'{5,6},'{7,8},'{5,6},'{7,8},'{5,6}};    
    $display("Testbench: A = %p", A);
    $display("Testbench: B = %p", B);

    // while (done == 0) begin
    //   @(posedge clk);
    // end
    // $display("Acc = %p ", C);
    // clear = 1;
    
  end

      // Reference Model
  task automatic golden_matmul_2x2_kn(
    input logic signed [15:0] A_t [M][K],
    input logic signed [15:0] B_t [K][N],
    output logic signed [31:0] C_ref [M][N]
  );
    int i, j, k;
    begin
      // int i, j, k;
        
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
          for (k=0; k<5; ++k) begin
              C_ref[i][j] += A_t[i][k] * B_t[k][j];
          end
        end
      end
      // $display("C_ref = %p", C_ref);
    end
  endtask


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
