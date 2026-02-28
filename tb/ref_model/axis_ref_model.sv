class axis_ref_model;

  typedef bit [31:0] data_t;
  data_t exp_pkt[$];   // expected C packet (one packet at a time)

  bit [31:0] acc = 0;
  // bit [63:0] acc;

  int N;
  int i, j, k;

  function void build_expected(
      input data_t a_pkt[$],
      input data_t b_pkt[$]
  );
    exp_pkt.delete();

    // Derive matrix dimension
    N = $rtoi($sqrt(a_pkt.size()));
    if (N*N != a_pkt.size() || b_pkt.size() != a_pkt.size()) begin
      $fatal("REF", "Invalid packet size for matmul");
    end

    for (i = 0; i < N; i++) begin
      for (j = 0; j < N; j++) begin
        acc = 0;
        for (k = 0; k < N; k++) begin
          acc += a_pkt[i*N + k] * b_pkt[k*N + j];
        end
        exp_pkt.push_back(acc[31:0]);
      end
    end
  endfunction

endclass