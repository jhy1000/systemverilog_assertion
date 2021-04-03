
module my_arb(...);

    always @* begin // arbiter code
        ...
    end

    assert property (@(posedge clk) disable iff (reset)
        !(grant[0] & grant[1]));

endmodule
