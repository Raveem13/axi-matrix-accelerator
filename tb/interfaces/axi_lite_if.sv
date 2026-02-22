interface axi_lite_if (input logic ACLK, input logic ARST_N);

  // Write Address
  logic        awvalid;
  logic        awready;
  logic [31:0] awaddr;

  // Write Data
  logic        wvalid;
  logic        wready;
  logic [31:0] wdata;
  logic [3:0]  wstrb;

  // Write Response
  logic        bvalid;
  logic        bready;
  logic [1:0]  bresp;

  // Read Address
  logic        arvalid;
  logic        arready;
  logic [31:0] araddr;

  // Read Data
  logic        rvalid;
  logic        rready;
  logic [31:0] rdata;
  logic [1:0]  rresp;

  // -------------------------------------------------
  // AXI-Stream A / B / C
  // -------------------------------------------------
  logic         a_tvalid;
  logic         a_tready;
  logic  [31:0] a_tdata;
  logic         a_tlast;

  logic         b_tvalid;
  logic         b_tready;
  logic  [31:0] b_tdata;
  logic         b_tlast;

  logic         c_tvalid;
  logic         c_tready;
  logic  [31:0] c_tdata;
  logic         c_tlast;

endinterface
