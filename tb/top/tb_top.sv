import uvm_pkg::*;
`include "uvm_macros.svh"

module tb_top;

    logic clk = 0;
    always #5 clk = ~clk;

    axi_lite_if axi_if0(clk, rst_n);

    axi_matrix_accelerator dut0 (
        .clk              (clk),
        .rst_n            (rst_n),

        // AXI-Lite
        .s_axi_awvalid    (axi_if0.awvalid),
        .s_axi_awready    (axi_if0.awready),
        .s_axi_awaddr     (axi_if0.awaddr),
        .s_axi_wvalid     (axi_if0.wvalid),
        .s_axi_bresp      (axi_if0.bresp),
        .s_axi_wready     (axi_if0.wready),
        .s_axi_wdata      (axi_if0.wdata),
        .s_axi_bvalid     (axi_if0.bvalid),
        .s_axi_bready     (axi_if0.bready),
        .s_axi_arvalid    (axi_if0.arvalid),
        .s_axi_arready    (axi_if0.arready),
        .s_axi_araddr     (axi_if0.araddr),
        .s_axi_rresp      (axi_if0.rresp),
        .s_axi_rvalid     (axi_if0.rvalid),
        .s_axi_rready     (axi_if0.rready),
        .s_axi_rdata      (axi_if0.rdata),

        // AXI-Stream
        .s_axis_a_tvalid  (axi_if0.a_tvalid),
        .s_axis_a_tready  (axi_if0.a_tready),
        .s_axis_a_tdata   (axi_if0.a_tdata),
        .s_axis_a_tlast   (axi_if0.a_tlast),

        .s_axis_b_tvalid  (axi_if0.b_tvalid),
        .s_axis_b_tready  (axi_if0.b_tready),
        .s_axis_b_tdata   (axi_if0.b_tdata),
        .s_axis_b_tlast   (axi_if0.b_tlast),

        .m_axis_c_tvalid  (axi_if0.c_tvalid),
        .m_axis_c_tready  (axi_if0.c_tready),
        .m_axis_c_tdata   (axi_if0.c_tdata),
        .m_axis_c_tlast   (axi_if0.c_tlast)

        // .done             (done)
    );

    initial begin
        uvm_config_db#(virtual axi_lite_if)::set(null, "*", "vif", axi_if0);
        run_test("base_test");
    end
endmodule

/*
Concept
    -run_test() hands control to UVM
    -No manual instantiation
*/