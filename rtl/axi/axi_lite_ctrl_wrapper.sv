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
    input   logic s_axi_bready,

    // ----Read----
    input  logic [ADDR_W-1:0]    s_axi_araddr,
    input  logic       s_axi_arvalid,
    output logic       s_axi_arready,

    output logic [DATA_W-1:0]    s_axi_rdata,
    output logic [1:0] s_axi_rresp,
    output logic       s_axi_rvalid,
    input  logic       s_axi_rready,
    // ========================

    // ========================
    // Compute core interface
    output logic [31:0]  cfg_m,
    output logic [31:0]  cfg_k,
    output logic [31:0]  cfg_n,

    output logic    start,
    input  logic    done
    // ========================    

);
    logic [DATA_W-1:0] ctrl_reg;
    logic [DATA_W-1:0] status_reg;
    logic [DATA_W-1:0] cfg_m_reg;
    logic [DATA_W-1:0] cfg_n_reg;
    logic [DATA_W-1:0] cfg_k_reg;

    logic start_pulse;

    bit write_fire, write_ok, read_ok;

    logic aw_hs, w_hs, ar_hs;

    logic [DATA_W-1:0] read_data;

    always_comb begin
        aw_hs = s_axi_awvalid &&  s_axi_awready;
        w_hs = s_axi_wvalid &&  s_axi_wready;
        
        write_fire = aw_hs && w_hs;

        write_ok =  (s_axi_awaddr == 32'h00) ||
                    (s_axi_awaddr == 32'h08) ||
                    (s_axi_awaddr == 32'h0C) ||
                    (s_axi_awaddr == 32'h10);

        ar_hs = s_axi_arvalid &&  s_axi_arready;
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
            // $display("%t [DUT] state = %s, data = %0d @ address = %h, BRESP = %02b, BVALID = %0d",
            //         $time, wstate.name(), s_axi_wdata, s_axi_awaddr, s_axi_bresp, s_axi_bvalid);
            wstate <= next_wstate;
        end
    end

    // Write Comb. logic
    always_comb begin
        s_axi_awready   =   0;   
        s_axi_wready    =   0;    
        s_axi_bvalid    =   0;   

        next_wstate     = wstate;

        case (wstate)
            W_IDLE  :   begin
                s_axi_awready   = 1;   
                s_axi_wready    = 1;  
                if (aw_hs && w_hs) begin
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

    logic [1:0] bresp_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bresp_reg   <= 2'b0;
        end
        else if (write_fire) begin
            bresp_reg   <= write_ok ? 2'b00 : 2'b10;
        end
        // $display("%t [%s] start = %0d , status[0] = %0d, control[0] = %0d",  $time, wstate.name(), start, status_reg[0], ctrl_reg[0]);    
    end

    assign s_axi_bresp = bresp_reg;
    // --------------

    // ----Read FSM----
    // Read data mux
    always_comb begin
        read_data = 32'd0;
        read_ok   = 1'b1;

        case (s_axi_araddr[7:0])
            8'h00: read_data = ctrl_reg;
            8'h04: read_data = status_reg;
            8'h08: read_data = cfg_m_reg;
            8'h0C: read_data = cfg_k_reg;
            8'h10: read_data = cfg_n_reg;
            default: begin
            read_data = 32'd0;
            read_ok   = 1'b0;
            end
        endcase
    end

    // Read FSM
    typedef enum logic {
        R_IDLE,
        R_DATA
    } rstate_t;

    rstate_t rstate, next_rstate;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rstate <= R_IDLE;
        else
            rstate <= next_rstate;
    end

    always_comb begin
    // defaults
        s_axi_arready = 0;
        s_axi_rvalid  = 0;
        next_rstate      = rstate;

        case (rstate)
            R_IDLE: begin
                s_axi_arready = 1;
                if (ar_hs) begin
                    next_rstate = R_DATA;
                end
            end

            R_DATA: begin
                s_axi_rvalid = 1;
                if (s_axi_rready) begin
                    next_rstate = R_IDLE;
                end
            end
        endcase
    end

    logic [1:0] rresp_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rresp_reg   = 2'b0;
            s_axi_rdata = 32'd0;
        end
        else if (ar_hs) begin
            rresp_reg   = read_ok ? 2'b00 : 2'b10;
            s_axi_rdata = read_data;
        end
        // $display("%t [%s] start = %0d , status[0] = %0d, control[0] = %0d",  $time, rstate.name(), start, status_reg[0], ctrl_reg[0]);    
    end

    assign s_axi_rresp = rresp_reg;
    //----MAC/Compute core controls----
    assign cfg_m = cfg_m_reg;
    assign cfg_k = cfg_k_reg;
    assign cfg_n = cfg_n_reg;

    // Start pulse logic
    logic ctrl_start;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            ctrl_start  <= 1'b0;
        else if (start)
            // CTRL[0] is self-clearing START bit (write 1 to trigger)
            ctrl_reg[0] <= 1'b0;    // 1'b0;    
        else
            ctrl_start  <= ctrl_reg[0];
    end

    assign start = ctrl_reg[0] & ~ctrl_start;

    // STATUS logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            status_reg      <= 32'd0;
        else if (start)
            status_reg[0]   <= 1'b0;    // clear on new start
        else if (done)
            status_reg[0]   <= 1'b1;      // latch completion
        // $display("%t start = %0d , done = %0d, ctrl_start = %0d, status[0] = %0d, control[0] = %0d",  $time, start, done, ctrl_start, status_reg[0], ctrl_reg[0]);    
    end

`ifndef SYNTHESIS

// A. Start is one-cycle pulse
assert property (@(posedge clk)
    start |-> ##1 !start
) 
else $fatal("start not single-cycle");

// B. Start only from CTRL write
assert property (@(posedge clk)
    start |-> $past(write_fire && s_axi_awaddr == 32'h00)
) 
else $fatal("START without CTRL write");

// C. STATUS latches done
assert property (@(posedge clk)
    done |=> status_reg[0] 
) 
else $fatal("STATUS did not latch DONE");

// D. STATUS clears on new start
assert property (@(posedge clk)
    start |=> !status_reg[0] 
) 
else $fatal("STATUS not cleared on new start");


// E. AXI write response eventually completes
assert property (@(posedge clk)
    write_fire |-> ##[1:5] s_axi_bvalid
) 
else $fatal("No BRESP after write");


`endif

endmodule
