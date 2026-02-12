module axi_lite_ctrl_wrapper #(
    parameter DATA_W = 32,
    parameter ADDR_W = 32
)(
    input   logic   clk,
    input   logic   rst_n,
    
    // ========================
    // AXI-Lite Slave interface
    // ========================
    // ---- Write ----   
    input   logic [ADDR_W-1:0]  s_axi_awaddr,
    input   logic s_axi_awvalid,
    output   logic s_axi_awready,

    input   logic [DATA_W-1:0]  s_axi_wdata,
    input   logic s_axi_wvalid,
    output   logic s_axi_wready,

    output   logic s_axi_bvalid,
    output   logic [1:0] s_axi_bresp,
    input   logic s_axi_bready

    // ----Read----

    // ========================

    // ========================
    // Compute core interface

    // ========================    

);
    logic [DATA_W-1:0] ctrl_reg;
    logic [DATA_W-1:0] status_reg;
    logic [DATA_W-1:0] cfg_m_reg;
    logic [DATA_W-1:0] cfg_n_reg;
    logic [DATA_W-1:0] cfg_k_reg;

    logic ctrl_start;
    logic start_pulse;

    logic write_fire, write_ok;

    logic aw_hs, w_hs;

    logic [DATA_W-1:0] read_data;

    always_comb begin
        aw_hs = s_axi_awvalid &&  s_axi_awready;
        w_hs = s_axi_wvalid &&  s_axi_wready;
        
        write_fire = aw_hs && w_hs;

        write_ok =  (s_axi_awaddr == 32'h00) ||
                    (s_axi_awaddr == 32'h08) ||
                    (s_axi_awaddr == 32'h0C) ||
                    (s_axi_awaddr == 32'h10);
    end
    

    //----Write FSM----
    // Write data MUX
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg    <= 32'd0;
            cfg_m_reg   <= 32'd0;
            cfg_n_reg   <= 32'd0;
            cfg_k_reg   <= 32'd0;
            // start = 0;
        end
        else if (aw_hs && w_hs) begin
            case (s_axi_awaddr[7:0])
                8'h00   : ctrl_reg <= s_axi_wdata;
                8'h08   : cfg_m_reg <= s_axi_wdata;
                8'h0C   : cfg_k_reg <= s_axi_wdata;
                8'h10   : cfg_n_reg <= s_axi_wdata;
                default : s_axi_bresp <= 2'b10;
            endcase
        end
    end

    typedef enum logic [1:0] { 
        W_IDLE,
        W_RESP

    } wstate_t;

    wstate_t wstate, next_wstate;

    // Write Seq logic
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            wstate <= W_IDLE;
        end else begin
            wstate <= next_wstate;
        end
    end

    // Write Comb. logic
    always_comb begin
        s_axi_awready   =   0;   
        s_axi_wready    =   0;    
        s_axi_bvalid    =   0;   
        s_axi_bresp     =   2'b00;
        write_fire      =   0;

        next_wstate     = wstate;

        case (wstate)
            W_IDLE  :   begin
                s_axi_awready   = 1;   
                s_axi_wready    = 1;  
                if (aw_hs && w_hs) begin
                    write_fire  = 1;
                    s_axi_bresp <= write_ok ? 2'b00 : 2'b10;
                    next_wstate = W_RESP;
                end
            end

            W_RESP  :   begin
                s_axi_bvalid    = 1;
                if (s_axi_bready) begin
                    next_wstate = W_IDLE;
                end
            end
        endcase
    end
    // --------------

    // ----Read FSM----

endmodule
