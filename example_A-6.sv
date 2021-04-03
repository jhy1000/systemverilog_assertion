
// Systemverilog concurrent assertion syntax

assert property
    (@(posedge clk) disable iff (reset) !(grant[0] & grant[1]))
else begin
    // See Appendix B, "Complete OVM/AVM TestBench example" for OVM details
    status = new();
    status.set_err_grant_mutex();
    status_ap.write(status);
end


