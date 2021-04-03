// Example A-3 Immediate check for mutually exclusive grants
module my_arb(...);

    always @* begin // arbiter code
        ...
    end

    assert property （@(posedge clk) !(grant[0] &grant[1]));

endmodule


// Format1 -- Inline expression

concurrent_assertion_name:
    assert
        property (
            @(posedge clk) disable iff (rst)
            req |-> ##3 gnt
        )
        else
            $error("%m no grant after request");


// Format2 --Separate property block
property ConcurrentPropName;
    @(posedge clk) disable iff(rst)
    req |-> ##3 gnt;
endproperty
AssertionName: assert property (ConcurrentPropName);

// The above example shows the general structure of a concurrent expression.
// The assertion is disable during reset.
// The variables in the expression are sampled at the edge of the clock specified.
// The expression checks if a grant gnt arrives 3 clocks after request req is made.
// If the expression returns false, an error is reported.


// I like to think of concurrent assertions as if statements within an always_ff block, Like this

// This is just dummy code. It's an alternate way to think of concurrent assertion
always_ff @(posedge clk) begin
    if (rst) begin
        // in rst
    end else begin
        if (assertion_expression)
            // do nothing
        else
            $error("fail");
        end
    end
end

/*
When you look at examples of concurrent assertions, you'll see |-> and  |=> operators frequently used. 
Thess are called implication operators and the LHS of the operator is called the antecedent and the RHS is called the consequent.

|->: Overlapping implication - The RHS is evaluated from the same cycle LHS is true
|=>: Non-overlapping implication - The RHS is evaluated one cycle after LHS is true

*/


// If inputs vld=1 and dat=8'h55, then ack is high 3 cycles later.

// The RHS is evaluated from the same cycle LHS is true
valid_gnt_chk: assert 
            property(
                @(posedge clk) disable iff (rst)
                (vld && dat == 8'h55) |-> ##3 ack
            );

// The RHS is evaluated one clock after LHS is true
valid_gnt_chk: assert
            property(
                @(posedge clk) disable iff(rst)
                (vld && dat == 8'h55) |=> ##2 ack
            );





