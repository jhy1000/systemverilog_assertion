
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



