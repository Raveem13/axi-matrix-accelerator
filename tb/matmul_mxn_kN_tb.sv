module matmul_mxn_kN_tb #(
    parameter DATA_W = 8,
    parameter ACC_W = 32,
    parameter int K = 3,
    parameter M = 3,
    parameter N = 3
    );
    
    logic clk;
    logic rst_n;
    logic start;

    logic signed [DATA_W-1:0] A [M][K] = '{default:0};
    logic signed [DATA_W-1:0] B [K][N] = '{default:0};

    logic signed [ACC_W-1:0] C [M][N];
    logic done;

    logic signed [ACC_W-1:0] C_ref[M][N];
    bit mismatch;

  // DUT
  matmul_mxn_kN #(
    .DATA_W(DATA_W), .ACC_W(ACC_W), .K(K), .M(M), .N(N)
  ) matmul_mxn_0(
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
    // A = '{'{1,2},'{3,4}};     // Expected C = A×B
    // B = '{'{5,6},'{7,8}};     // {{19,22},{43,50}}
    // Test 2
    A = '{'{1,2,3},'{3,4,5},'{6,7,8}};     // Expected C = A×B
    B = '{'{5,6,7},'{7,8,9},'{1,2,3}};    

    // while (done == 0) begin
    //   @(posedge clk);
    // end
    // $display("Acc = %p ", C);
    // clear = 1;
    
  end

    // Checker in Scoreboard
  always @(posedge clk) begin
    if (done) begin
      golden_matmul_mxn_kn(A, B, C_ref);

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
      for (int i=0; i<M; ++i) begin
        for (int j=0; j<N; ++j) begin
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
task automatic golden_matmul_mxn_kn(
  input logic signed [7:0] A [][],
  input logic signed [7:0] B [][],
  output logic signed [31:0] C_ref [3][3]
);
    
  begin
    int i, j, k;
    int M, N, K;

    M = A.size();
    N = B[0].size();
    K = A[0].size();

    // C_ref = new[M];
    // foreach (C_ref[i]) begin
    //   C_ref[i] = new[N];
    // end
    // $display("A = %p", A);
    // $display("B = %p", B);
    // $display("A size = %0d", A.size());

    // Initialize
    // foreach (C_ref[i]) begin
    //   foreach (C_ref[i][j]) begin
    //     C_ref[i][j] = '0;
    //   end
    // end
    C_ref = '{default:0};

    $display("Running Ref model");
    // Maatrix Multplication
    for (i=0; i<M; ++i) begin
      for (j=0; j<N; ++j) begin
        for (k=0; k<K; ++k) begin
            C_ref[i][j] += A[i][k] * B[k][j];
        end
      end
    end
    // $display("C_ref = %p", C_ref);
  end
endtask
