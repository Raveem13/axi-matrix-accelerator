class virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(virtual_sequencer)

    axi_lite_sequencer ctrl_seqr;
    axi_stream_sequencer a_seqr;
    axi_stream_sequencer b_seqr;
    axi_stream_sequencer c_seqr;

    axi_lite_monitor ctrl_mon;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass