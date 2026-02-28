class axis_ref_model;

  typedef bit [31:0] data_t;
  data_t exp_pkt[$];   // expected C packet (one packet at a time)

  function void build_expected(
      input data_t a_pkt[$],
      input data_t b_pkt[$]
  );
    exp_pkt.delete();

    foreach (a_pkt[i]) begin
      exp_pkt.push_back(a_pkt[i] + b_pkt[i]);
    end
  endfunction

endclass