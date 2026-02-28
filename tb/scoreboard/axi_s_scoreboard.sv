`uvm_analysis_imp_decl(_a)
`uvm_analysis_imp_decl(_b)
`uvm_analysis_imp_decl(_c)

class axi_s_scoreboard extends uvm_component;
    `uvm_component_utils(axi_s_scoreboard)
    
    axis_ref_model ref_model;

    // Queues
    bit [31:0] a_pkt[$];
    bit [31:0] b_pkt[$];
    bit [31:0] c_pkt[$];

    // Three subscribers
    uvm_analysis_imp_a #(axi_stream_packet, axi_s_scoreboard) ap_a;
    uvm_analysis_imp_b #(axi_stream_packet, axi_s_scoreboard) ap_b;
    uvm_analysis_imp_c #(axi_stream_packet, axi_s_scoreboard) ap_c;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        ref_model = new();

        ap_a = new("ap_a", this);
        ap_b = new("ap_b", this);
        ap_c = new("ap_c", this);

    endfunction

    function void write_a(axi_stream_packet pkt);
        a_pkt   = pkt.data;
        // try_build_expected();
    endfunction

    function void write_b(axi_stream_packet pkt);
        b_pkt   = pkt.data;
        // try_build_expected();
    endfunction

    function void write_c(axi_stream_packet pkt);
        try_build_expected();
        c_pkt = pkt.data;
        // $display("C_packet = %p", c_pkt);
        compare();
    endfunction

    function void try_build_expected();
        if (a_pkt.size() && b_pkt.size()) begin
            ref_model.build_expected(a_pkt, b_pkt);
        end
    endfunction

    function void compare();

        if (ref_model.exp_pkt.size() != c_pkt.size()) begin
            `uvm_error("SCB",
                $sformatf("Size mismatch: exp=%0d got=%0d",
                ref_model.exp_pkt.size(), c_pkt.size()))
            return;
        end

        foreach (c_pkt[i]) begin
            if (c_pkt[i] != ref_model.exp_pkt[i]) begin
                `uvm_error("SCB",
                    $sformatf("Mismatch at beat %0d: exp=%0d got=%0d",
                    i, ref_model.exp_pkt[i], c_pkt[i]))
                return;
            end
            else begin
                `uvm_info("SCB", $sformatf("i:%0d Exp=%0d, Got=%0d",
                        i, ref_model.exp_pkt[i], c_pkt[i] ), 
                        UVM_NONE)
            end
        end

        `uvm_info("SCB", "Matrix multiplication packet PASSED", UVM_LOW)
    endfunction
endclass