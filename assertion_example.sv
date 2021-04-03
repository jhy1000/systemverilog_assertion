

// FIFO level cannot go down without a pop.
property FifoLevelCheck;
    @(posedge clk) disable iff (rst)
    (!rd_vld) |-> ##1 (fifo_level >=  $past(fifo_level));
endproperty
FifoLevelCheck_c: assert property (FifoLevelCheck);


// When there's a no_space_err, the on_space_ctr_incr signal is flagged
// for exactly once clock
property NoSpaceErrCtr;
    @(posedge clk) disable iff (rst)
    (no_space_err) |-> (no_space_ctr_incr ^ $past(no_space_ctr_incr));
endproperty
NoSpaceErrCtr_A: assert property (NoSpaceErrCtr);



// If there's an uncorrectable err during an ADD request.
// err_cnt should be incremented in the same cycle and an interrupt
// should be flagged in the next clock.
property AddUncorErrCheck;
    @(posedge clk) disable iff (rst)
    (uncor_err && (req_type == ADD)) |->
    (err_cnt_incr ##1 intr);
endproperty
AddUncorErrCheck_A: assert property(AddUncorErrCheck);


// INIT and FLUSH transcations should complete within MAX_LATENCY.
property LatencyCheck;
    @(posedge clk) disable iff(rst)
    ((req_type == INIT) ||
     (req_type == FLUSH)) |-> (block_latency < MAX_LATENCY);
endproperty
LatencyCheck_A: assert property (LatencyCheck);


// interrupt should never get set.
property InterruptCheck;
    @(posedge clk) disable iff(rst)
    (!intr);
endproperty
InterruptCheck_A: assert property (InterruptCheck);


// wr_data should be stable until wr_ack arrives
property WriteData;
    @(posedge clk) disable iff (rst)
    (wr && !wr_ack) |-> ##1 (wr_data == $past(wr_data));
endproperty
WriteData_A: assert property(WriteData);


// wr_ack should be asserted only when there's a wr reqeust
property WriteAck;
    @(posedge clk) disable iff (rst)
    (!wr) |-> (!wr_ack);
endproperty
WriteAck_A: assert property(WriteAck);


// If wr is asserted, it should remain high until wr_ack is received
property WriteAck2;
    @(posedge clk) disable iff(rst)
    (wr && (!wr_ack)) |-> ##1 wr;
endproperty
WriteAck2_A: assert property (WriteAck2);


// output is not x or z when valid is high
DoutCheck: assert property (@(posedge clk) valid |-> (!$isnuknown(dout)));


// Check if ack arrives 3 to 5 clocks after a request
assert property (@(posedge clk) req |-> ##[3:5] ack);


// Check if interrupt propagates when intr is enabled
generate
    for (i=0; i<16; i++) begin: INTR0
        Intr0: assert property(@(posedge clk) disable iff (rst)
            ((intr_enable[i] & intr_status[i]) |-> ## intr))
        else
            `uvm_error("INTR_ERR", $sformatf("[%m]: Interrupt not propagating"))
    end
endgenerate


// When vld rises high -
// -- a is repeated twice then
// -- aster 2 clocks b is repeated 3 to 4 times with gaps in between.
// -- after last occurence of b, exactly 1 clock later c occurs.
// -- one clock after c, d occurs 3 times non-consecutively.
// -- after last occurence of d, there are a variable number of empty.
// -- clock, then a happens.
property Repeat1;
    @(posedge clk) disable iff (rst)
    $rose(vld) |-> (a[*2】 ##2 b[->3:4] ##1 c ##1 d[=3] ##1 e);
endproperty
Repeat1_A: assert property(Repeat1);




// Going craze with repetition operators
property Repeat2;
    @(posedge clk) diable iff(rst)
    $fell(reset) |-> ##[3:5] ((st1 ##6 st2)[*2]) ##2 (ready [*1:5]);
endproperty
Repeat2_A: assert property(Repeat2);



