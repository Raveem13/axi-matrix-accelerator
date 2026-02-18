interface axi_lite_if (input logic ACLK, input logic ARST_N);

  // Write Address
  logic        AWVALID;
  logic        AWREADY;
  logic [31:0] AWADDR;

  // Write Data
  logic        WVALID;
  logic        WREADY;
  logic [31:0] WDATA;
  logic [3:0]  WSTRB;

  // Write Response
  logic        BVALID;
  logic        BREADY;
  logic [1:0]  BRESP;

  // Read Address
  logic        ARVALID;
  logic        ARREADY;
  logic [31:0] ARADDR;

  // Read Data
  logic        RVALID;
  logic        RREADY;
  logic [31:0] RDATA;
  logic [1:0]  RRESP;

endinterface
