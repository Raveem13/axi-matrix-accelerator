//  Class: axi_stream_packet
//
class axi_stream_packet extends uvm_sequence_item;
    `uvm_object_utils(axi_stream_packet);

    //  Group: Variables
    rand bit [31:0] data[$];    // dynamic array of beats
    bit        last;

    //  Constructor: new
    function new(string name = "axi_stream_packet");
        super.new(name);
    endfunction
    
endclass
