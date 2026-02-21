typedef enum logic [2:0] {
        IDLE,
        LOAD_A,
        LOAD_B,
        PREPARE,
        COMPUTE,
        OUTPUT,
        DONE
    } state_t;

state_t state;

module cov_matmul (
    input logic        clk,
    input logic        rst_n,
    input logic        start,
    input logic        done,
    input logic [1:0]  state,
    input int          a_cnt,
    input int          b_cnt
);
    

    // FSM state coverage
    //  Covergroup: cg_fsm
    //
    covergroup cg_fsm @(posedge clk);
        option.per_instance =   1;
        //  Coverpoint: cp_state
        cp_state : coverpoint state {
            bins idle       = {IDLE};
            bins load_a     = {LOAD_A};
            bins load_b     = {LOAD_B};
            bins prepare    = {PREPARE};
            bins compute    = {COMPUTE};
            bins out        = {OUTPUT};
            bins done       = {DONE};
        }
    endgroup
    cg_fsm fsm_cov = new();

    // FSM Transition Coverage 
    //  Covergroup: cg_fsm_trans   
    covergroup cg_fsm_trans @(posedge clk);
        option.per_instance =   1;
        //  Coverpoint: cp_trans
        cp_trans: coverpoint state {
            bins idle_to_load_a     = (IDLE     =>  LOAD_A);
            bins load_a_to_load_b   = (LOAD_A   =>  LOAD_B);
            bins load_b_to_prep     = (LOAD_B   =>  PREPARE);
            bins prep_to_compute    = (IDLE     =>  LOAD_A);
            bins compute_to_out     = (COMPUTE  =>  OUTPUT);
            bins out_to_done        = (OUTPUT   =>  DONE);
            bins done_to_idle       = (DONE     =>  IDLE);             
        }
    endgroup: cg_fsm_trans
    cg_fsm_trans fsm_trans = new();

    // Reset Scenario Coverage
    covergroup cg_reset @(posedge clk);
        option.per_instance = 1;

        cp_reset_state : coverpoint state {
            bins reset_in_idle      = {IDLE};
            bins reset_in_load_a    = {LOAD_A};
            bins reset_in_load_b    = {LOAD_B};
            bins reset_in_compute   = {COMPUTE}; 
            bins reset_in_out       = {OUTPUT};
            bins reset_in_done      = {DONE};
        }

        cp_reset : coverpoint rst_n {
            bins asserted   = {0};
            bins deasserted = {1};
        }

        cross cp_reset, cp_reset_state;
    endgroup

    cg_reset reset_cov = new();
    
    // Start / Done Control Coverage
    covergroup cg_control @(posedge clk);
        option.per_instance = 1;

        cp_start : coverpoint start {
            bins start_low  = {0};
            bins start_high = {1};
        }

        cp_done : coverpoint done {
            bins done_low  = {0};
            bins done_high = {1};
        }

        cross cp_start, cp_done;
    endgroup

    cg_control ctrl_cov = new();

    // Stream Beat Count Coverage (A & B)
    covergroup cg_stream @(posedge clk);
        option.per_instance = 1;

        cp_a_cnt : coverpoint a_cnt {
            bins zero   = {0};
            bins partial= {[1:2]};
            bins full   = {3};   // 2x2 matrix = 4 beats
        }

        cp_b_cnt : coverpoint b_cnt {
            bins zero = {0};
            bins partial= {[1:2]};
            bins full = {3};
        }
        endgroup

    cg_stream stream_cov = new();

    // Multi-Run Coverage (Optional)
    int run_count;

    always @(posedge done)
    run_count++;

    covergroup cg_runs @(posedge clk);
        cp_runs : coverpoint run_count {
            bins one   = {1};
            bins multi = {[2:5]};
        }
    endgroup

    cg_runs run_cov = new();

endmodule

// NOTE:
// Cross cp_reset x cp_reset_state:
// reset asserted in load states is architecturally illegal.
// FSM forces IDLE on reset.
// Uncovered bins are expected and acceptable.