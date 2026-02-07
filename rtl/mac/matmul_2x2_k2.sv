module matmul_2x2_k2 #(
    parameter DATA_W = 8,
    parameter ACC_W = 32
)(
    input logic clk,
    input logic rst_n,
    input logic start,

    input logic signed [DATA_W-1:0] A [2][2],
    input logic signed [DATA_W-1:0] B [2][2],

    output logic signed [ACC_W-1:0] C [2][2],
    output logic done

);
    // internal signals
    logic en, clear;
    logic [1:0] k;
    logic signed [DATA_W-1:0] a_mac [2][2];
    logic signed [DATA_W-1:0] b_mac [2][2];

    typedef enum logic [2:0] {
        IDLE,
        CLEAR,
        K0,
        K1,
        DONE
    } state_t;

    state_t state;

    // K-loop control FSM
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            state <= IDLE;
            en    <= 0;
            clear <= 0;
            done  <= 0;
            k     <= 0;
        end else begin
            case (state)

                IDLE: begin
                    en    <= 0;
                    clear <= 0;
                    done  <= 0;
                    if (start)
                        state <= CLEAR;
                end

                CLEAR: begin
                    clear <= 1;   // one clean cycle
                    en    <= 0;
                    state <= K0;
                end

                K0: begin
                    clear <= 0;
                    en    <= 1;
                    k     <= 0;
                    state <= K1;
                end

                K1: begin
                    en    <= 1;
                    k     <= 1;
                    state <= DONE;
                end

                DONE: begin
                    en   <= 0;
                    done <= 1;
                end

            endcase
        end
    end

// Data mapping
    always_comb begin
        // k = 0
        if (k == 0) begin
            // $display("k=0: A = %p ", A);
            // $display("k=0: B = %p ", B);
            a_mac[0][0] = A[0][0]; b_mac[0][0] = B[0][0];
            a_mac[0][1] = A[0][0]; b_mac[0][1] = B[0][1];
            a_mac[1][0] = A[1][0]; b_mac[1][0] = B[0][0];
            a_mac[1][1] = A[1][0]; b_mac[1][1] = B[0][1];
            // $display("k=0: A_mac = %p ", a_mac);
            // $display("k=0: B_mac = %p ", b_mac);

        end 
        // k = 1
        else begin
            // $display("k=1: A = %p ", A);
            // $display("k=1: B = %p ", B);
            a_mac[0][0] = A[0][1]; b_mac[0][0] = B[1][0];
            a_mac[0][1] = A[0][1]; b_mac[0][1] = B[1][1];
            a_mac[1][0] = A[1][1]; b_mac[1][0] = B[1][0];
            a_mac[1][1] = A[1][1]; b_mac[1][1] = B[1][1];
            // $display("k=1: A_mac = %p ", a_mac);
            // $display("k=1: B_mac = %p ", b_mac);

        end
    end

    mac_array_2x2   mac_array (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .clear(clear),
        .a(a_mac),
        .b(b_mac),
        .acc(C) 
    );
    
endmodule