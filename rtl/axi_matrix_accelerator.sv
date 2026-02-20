module axi_matrix_accelerator #(
    parameter ADDR_W = 32,
    parameter DATA_W = 32
) (
    input  logic clk,
    input  logic rst_n,

    // =========================
    // AXI-Lite (Control Plane)
    // =========================
    // Write address
    input  logic [ADDR_W-1:0] s_axi_awaddr,
    input  logic        s_axi_awvalid,
    output logic        s_axi_awready,
    
    // Write data
    input  logic [DATA_W-1:0] s_axi_wdata,
    input  logic        s_axi_wvalid,
    output logic        s_axi_wready,

    // Write response
    output logic        s_axi_bvalid,
    output logic [1:0]  s_axi_bresp,
    input  logic        s_axi_bready,

    // Read address
    input  logic [ADDR_W-1:0] s_axi_araddr,
    input  logic        s_axi_arvalid,
    output logic        s_axi_arready,

    // Read data
    output logic [DATA_W-1:0] s_axi_rdata,
    output logic [1:0]  s_axi_rresp,
    output logic        s_axi_rvalid,
    input  logic        s_axi_rready,

    // =========================
    // AXI-Stream A (Matrix A)
    // =========================
    input  logic [DATA_W-1:0] s_axis_a_tdata,
    input  logic        s_axis_a_tvalid,
    output logic        s_axis_a_tready,
    input  logic        s_axis_a_tlast,

    // =========================
    // AXI-Stream B (Matrix B)
    // =========================
    input  logic [DATA_W-1:0] s_axis_b_tdata,
    input  logic        s_axis_b_tvalid,
    output logic        s_axis_b_tready,
    input  logic        s_axis_b_tlast,

    // =========================
    // AXI-Stream C (Result)
    // =========================
    output logic [DATA_W-1:0] m_axis_c_tdata,
    output logic        m_axis_c_tvalid,
    input  logic        m_axis_c_tready,
    output logic        m_axis_c_tlast

     // ------------------------
    // Control / Status (VISIBLE)
    // ------------------------
    // output logic              done
);

    localparam N = 2;

    // -------------------------
    // Internal control signals
    // -------------------------
    logic        start = 0;
    logic        done;
    logic [15:0] cfg_k;

    // -------------------------
    // AXI-Lite Control Wrapper
    // -------------------------
    axi_lite_ctrl_wrapper #(
        .DATA_W (DATA_W),
        .ADDR_W (ADDR_W)
    ) u_ctrl (
        .clk            (clk),
        .rst_n          (rst_n),

        // AXI-Lite write
        .s_axi_awaddr   (s_axi_awaddr),
        .s_axi_awvalid  (s_axi_awvalid),
        .s_axi_awready  (s_axi_awready),

        .s_axi_wdata    (s_axi_wdata),
        .s_axi_wvalid   (s_axi_wvalid),
        .s_axi_wready   (s_axi_wready),

        .s_axi_bvalid   (s_axi_bvalid),
        .s_axi_bresp    (s_axi_bresp),
        .s_axi_bready   (s_axi_bready),

        // AXI-Lite read
        .s_axi_araddr   (s_axi_araddr),
        .s_axi_arvalid  (s_axi_arvalid),
        .s_axi_arready  (s_axi_arready),

        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rvalid   (s_axi_rvalid),
        .s_axi_rready   (s_axi_rready),

        // Control outputs
        .cfg_k          (cfg_k),
        .start          (start),
        .done           (done)
    );

    // -------------------------
    // Compute Wrapper
    // -------------------------

    compute_wrapper #(
        .DATA_W (DATA_W)
    ) u_compute (
        .clk                (clk),
        .rst_n              (rst_n),

        // AXI-Stream A
        .s_axis_a_tdata     (s_axis_a_tdata),
        .s_axis_a_tvalid    (s_axis_a_tvalid),
        .s_axis_a_tready    (s_axis_a_tready),
        .s_axis_a_tlast     (s_axis_a_tlast),

        // AXI-Stream B
        .s_axis_b_tdata     (s_axis_b_tdata),
        .s_axis_b_tvalid    (s_axis_b_tvalid),
        .s_axis_b_tready    (s_axis_b_tready),
        .s_axis_b_tlast     (s_axis_b_tlast),

        // AXI-Stream C
        .m_axis_c_tdata     (m_axis_c_tdata),
        .m_axis_c_tvalid    (m_axis_c_tvalid),
        .m_axis_c_tready    (m_axis_c_tready),
        .m_axis_c_tlast     (m_axis_c_tlast),

        // Control
        .cfg_k              (cfg_k), 
        .start              (start),
        .done               (done)
    );

endmodule