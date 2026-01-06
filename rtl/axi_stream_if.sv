`timescale 1ns / 1ps

interface axi_stream_if (
    input wire clk,
    rst
);
  logic TLAST;  // This shall be set by the testbench
  var real TDATA;  // Payload
  var logic TREADY;  //Datapath sync (use in FSM would break axi)
  var logic TVALID;  // This and TLAST are FSM language
  //tuser is overflow, tid and others are ommited as allowed by the standard

  // axi streams transactions are implemnted with clockings
  clocking cb_master @(posedge clk);
    default input #0.1 output #0.1;

    output TDATA, TVALID, TLAST;
    input TREADY;
  endclocking

  clocking cb_slave @(posedge clk);
    default input #0.1 output #0.1;

    output TREADY;
    input TDATA, TVALID, TLAST;
  endclocking

  // 2 communication paths, directions are inverted
  modport master(clocking cb_master);
  modport slave(clocking cb_slave);  // As seen from the interface


  property valid_is_not_deasserted_untill_handshake;
    @(posedge clk) disable iff (rst) TVALID && !TREADY |-> ##1 TVALID;
  endproperty
  assert property (valid_is_not_deasserted_untill_handshake);

  property no_deadlock_before_handshake;
    @(posedge clk) disable iff (rst) TVALID |-> ##[0:$] TREADY;
  endproperty
  assert property (no_deadlock_before_handshake);

  property hold_backpressure;
    @(posedge clk) disable iff (rst) TVALID && !TREADY |-> $stable(
        TDATA
    ) && $stable(
        TLAST
    );
  endproperty
  assert property (hold_backpressure);

  property data_is_not_changed_once_valid_untill_handshake;
    @(posedge clk) disable iff (rst) TVALID && !TREADY |-> $stable(
        TDATA
    );
  endproperty

  property valid_on_last;
    @(posedge clk) disable iff (rst) TLAST |-> TVALID;
  endproperty
  assert property (valid_on_last);

endinterface
