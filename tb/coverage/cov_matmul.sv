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

    //  Covergroup: cg_fsm_trans   
    //
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

endmodule