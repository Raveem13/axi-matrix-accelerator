//  Interface: axi_stream_if
//
interface axi_stream_if #(
        int DW = 32
    )(
        input logic ACLK,
        input logic ARST_N
    );
    logic [DW-1:0]  TDATA;
    logic           TVALID;
    logic           TREADY;
    logic           TLAST;    
endinterface
