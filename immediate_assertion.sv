
// in many respects, an immediate assertion is similar to an if statement.
// They check to see if a conditional expression holds, and if not, then the simulator generates an error message.

// For instance, Example A-1 demonstrates a portion of some procedural code associated with an aribiter design where a procedural if statement checks that two of the arbiter's grant signals are never active at the same time.

// Example A-1 immediate check for mutually exclusive grants
module my_arb(...);

    always @* begin // arbiter code
        ....
        if (grant[0] & grant[1])
            $display("Mutex violation for grant[0] and grant[1]");
        ....
    end

endmodule


// Example A-2 Immediate check for mutually exclusive grants
module my_arb(...);

    always @* begin // arbiter code
        ....
        assert (!(grant[0] & grant[1]));
        ....
    end

endmodule



immediate_assertion:
    assert (current_state != 0)
    else
        $error("%m checker failed);



// This is just dummy code. It's an alternate way to think of immediate assertion.
always_comb begin
    if (assertion statement)
        // do nothing;
    else
        $error("fail");
end



