`ifndef AXI_STREAM_IF_SV
`define AXI_STREAM_IF_SV

`timescale 1ns / 1ps

typedef struct packed {
  logic unsigned [63:0] TDATA;
  logic TVALID, TLAST;
} axi_stream_mastero_slavei_t;
typedef struct packed {logic TREADY;} axi_stream_masteri_slaveo_t;

// Apperantly, interfaces are not supported by Icarus
/*interface axi_stream_if (
    input wire clk,
    rst
);
  logic TLAST;  // This shall be set by the testbench
  var logic unsigned [63:0] TDATA;  // Payload
  var logic TREADY;  //Datapath sync (use in FSM would break axi)
  var logic TVALID;  // This and TLAST are FSM language
  //tuser is overflow, tid and others are ommited as allowed by the standard

  // axi streams transactions are implemnted with clockings
  clocking cb_master @(posedge clk);
    default input #0.1 output #0.1;

    output TDATA, TVALID, TLAST;
    input TREADY;
  endclocking  // Not supported by Icarus

  clocking cb_slave @(posedge clk);
    default input #0.1 output #0.1;

    output TREADY;
    input TDATA, TVALID, TLAST;
  endclocking

  // 2 communication paths, directions are inverted
  //modport master(clocking cb_master);
  //modport slave(clocking cb_slave);  // As seen from the interface
  // V-word doesn't support skews, should be fine anyway
  //modport master(output TDATA, TVALID, TLAST, input TREADY);
  //modport slave(input TDATA, TVALID, TLAST, output TREADY);
  // Icarus doesn't support modport

  //property valid_is_not_deasserted_untill_handshake;
  //@(posedge clk) disable iff (rst) (TVALID && !TREADY) |-> ##1 TVALID;
  //assert property (valid_is_not_deasserted_untill_handshake);
  // Supposedly the same? V-word-friendly
  reg tv_valid_d;
  always @(posedge clk)
    if (rst) tv_valid_d <= 0;
    else tv_valid_d <= TVALID;
  always @(posedge clk) begin
    if (!rst && TVALID && !TREADY) begin
      if (!tv_valid_d) $error("TVALID dropped before handshake");
    end
  end

  //property no_deadlock_before_handshake;
  //  @(posedge clk) disable iff (rst) TVALID |-> ##[0:$] TREADY; 
  //  // V-word doesnt support delays either
  //endproperty
  //assert property (no_deadlock_before_handshake);

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
  assert property (valid_on_last);  // Not supported by Icarus

endinterface*/

`endif
