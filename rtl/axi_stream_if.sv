`ifndef AXI_STREAM_IF_SV
`define AXI_STREAM_IF_SV

`timescale 1ns / 1ps

typedef struct packed {
  logic [63:0] TDATA;
  logic TVALID, TLAST;
} axi_stream_mastero_slavei_t;
typedef struct packed {logic TREADY;} axi_stream_masteri_slaveo_t;

interface axi_stream_if (
    input wire clk,
    rst
);
  logic TLAST;  // This shall be set by the testbench
  var logic [63:0] TDATA;  // Payload
  var logic TREADY;  //Datapath sync (use in FSM would break axi)
  var logic TVALID;  // This and TLAST are FSM language
  //tuser is overflow, tid and others are ommited as allowed by the standard

  // axi streams transactions are implemnted with clockings
  /*clocking cb_master @(posedge clk);
    default input #0.1 output #0.1;

    output TDATA, TVALID, TLAST;
    input TREADY;
  endclocking*/  // Not supported by Icarus

  /*clocking cb_slave @(posedge clk);
    default input #0.1 output #0.1;

    output TREADY;
    input TDATA, TVALID, TLAST;
  endclocking*/

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

  /*property hold_backpressure;
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
  assert property (valid_on_last);*/  // Not supported by Icarus

  // Delayed signal registers
  reg [63:0] tdata_d;
  reg tlast_d;
  reg tvalid_and_not_ready_d;

  // hold_beckpressure
  always @(posedge clk) begin
    if (rst) begin
      tv_valid_d <= 0;
    end else begin
      tv_valid_d <= TVALID;
      if (!rst && TVALID && !TREADY && !tv_valid_d) begin
        $error("TVALID deasserted during backpressure at %0t", $time);
      end
    end
  end

  // data_is_not_changed_once_valid_untill_handshake
  always @(posedge clk) begin
    if (rst) begin
      tdata_d <= 0;
      tlast_d <= 0;
    end else begin
      tdata_d <= TDATA;
      tlast_d <= TLAST;

      if (!rst && TVALID && !TREADY) begin
        if (tdata_d !== TDATA) $error("TDATA changed during backpressure");
        if (tlast_d !== TLAST) $error("TLAST changed during backpressure");
      end
    end
  end

  // valid_on_last
  always @(posedge clk) begin
    if (!rst && TLAST && !TVALID) begin
      $error("TLAST without TVALID at %0t", $time);
    end
  end

  // no_deadlock_before_handshake
  reg [7:0] backpressure_count;
  always @(posedge clk) begin
    if (rst) begin
      backpressure_count <= 0;
    end else if (TVALID && !TREADY) begin
      backpressure_count <= backpressure_count + 1;
      if (backpressure_count > 100) begin  // Timeout
        $error("Backpressure > 100 cycles at %0t", $time);
        $finish;
      end
    end else begin
      backpressure_count <= 0;
    end
  end

  // Data transfer only on handshake
  logic handshake_d, data_accepted_d;
  always @(posedge clk) begin
    if (rst) begin
      handshake_d <= 0;
      data_accepted_d <= 0;
    end else begin
      handshake_d <= TVALID && TREADY;
      data_accepted_d <= handshake_d;  // Previous cycle's handshake

      // No internal data change without handshake
      if (!rst && !handshake_d && data_accepted_d !== 1'bx) begin
        if (tdata_d != TDATA) $error("Data changed without handshake");
      end
    end
  end

endinterface

`endif
