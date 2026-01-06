`ifndef HORNER_CUBIC_FSM_SV
`define HORNER_CUBIC_FSM_SV

`timescale 1ns / 1ps

`include "axi_stream_if.sv"

module horner_cubic_stage_fsm #(
    parameter real MULT,  // ISO 754 floating point
    parameter real CONST
) (
    input rst,
    clk,
    input axi_stream_mastero_slavei_t previ,  // Slave to the previous
    output axi_stream_masteri_slaveo_t prevo,
    input axi_stream_masteri_slaveo_t nexti,
    output axi_stream_mastero_slavei_t nexto  // Maaster to the next
);
  var real mult = (MULT);  // reinterpret_cast
  var real c = (CONST);
  real data, res;
  // Moore FSM for protocol
  typedef enum logic [1:0] {
    IDLE = 2'b00,
    LOAD = 2'b01,
    RES  = 2'b10
  } state_t;

  state_t state, next_state;

  always_comb begin
    next_state = state;
    unique case (state)
      IDLE: if (previ.TVALID) next_state = LOAD;
      LOAD: next_state = RES;
      RES:  if (nexti.TREADY) next_state = IDLE;
    endcase
  end

  always_ff @(posedge clk) begin  // Update state
    if (rst) state <= IDLE;
    else state <= next_state;
  end


  // Datapath
  // Output evaluation
  always_comb begin
    data = 0;
    if ((state == IDLE) && previ.TVALID) data = $bitstoreal(previ.TDATA);
  end
  always_comb begin
    res = 0;
    if (state == LOAD) res = data * mult + c;
  end
  // Output propagation
  always_ff @(clk) begin  // Ready in wait, otherwise not
    prevo.TREADY <= (state == IDLE);
  end
  always_ff @(clk) begin  // Result accumulation here, if ready
    nexto.TVALID <= (state == RES);
    nexto.TDATA  <= (state == RES) ? $realtobits(res) : 0;
    nexto.TLAST  <= (state == RES) ? previ.TLAST : '0;
    // Next has cb_master, prev has cb_slave, removed for verilator compatibility
  end

  // Verification (Icarus has no property support, and no interface support,
  // so this is the only way) (Verilator has no program and task support, so that is
  // even worse)

  reg tv_valid_d;
  always @(posedge clk)
    if (rst) tv_valid_d <= 0;
    else tv_valid_d <= nexto.TVALID;
  always @(posedge clk) begin
    if (!rst && nexto.TVALID && !nexti.TREADY) begin
      if (!tv_valid_d) $error("TVALID dropped before handshake");
    end
  end

  // Delayed signal registers
  reg [63:0] tdata_d;
  reg tlast_d;
  reg tvalid_and_not_ready_d;

  // hold_beckpressure
  always @(posedge clk) begin
    if (rst) begin
      tv_valid_d <= 0;
    end else begin
      tv_valid_d <= nexto.TVALID;
      if (!rst && nexto.TVALID && !nexti.TREADY && !tv_valid_d) begin
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
      tdata_d <= previ.TDATA;
      tlast_d <= previ.TLAST;

      if (!rst && nexto.TVALID && !nexti.TREADY) begin
        if (tdata_d !== nexto.TDATA) $error("TDATA changed during backpressure");
        if (tlast_d !== nexto.TLAST) $error("TLAST changed during backpressure");
      end
    end
  end

  // valid_on_last, the only slave-side check!
  always @(posedge clk) begin
    if (!rst && previ.TLAST && !previ.TVALID) begin
      $error("TLAST without TVALID at %0t", $time);
    end
  end

  // no_deadlock_before_handshake
  reg [7:0] backpressure_count;
  always @(posedge clk) begin
    if (rst) begin
      backpressure_count <= 0;
    end else if (nexto.TVALID && !nexti.TREADY) begin
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
      handshake_d <= nexto.TVALID && nexti.TREADY;
      data_accepted_d <= handshake_d;  // Previous cycle's handshake

      // No internal data change without handshake
      if (!rst && !handshake_d && data_accepted_d !== 1'bx) begin
        if (tdata_d != nexto.TDATA) $error("Data changed without handshake");
      end
    end
  end

endmodule

// Assembling the pipeline
module horner_cubic_fsm #(
    parameter real A,
    parameter real B,
    parameter real C,
    parameter real D
) (
    input clk,
    rst,
    input axi_stream_mastero_slavei_t abtbi,  // Slave to the previous
    output axi_stream_masteri_slaveo_t abtbo,
    input axi_stream_masteri_slaveo_t cdtbi,
    output axi_stream_mastero_slavei_t cdtbo  // Maaster to the next
);
  axi_stream_mastero_slavei_t abbco_bcabi;  // Slave to the previous
  axi_stream_masteri_slaveo_t abbci_bcabo;  // Naming conv: masterview_slaveview

  axi_stream_masteri_slaveo_t bccdi_cdbco;
  axi_stream_mastero_slavei_t bccdo_cdbci;  // Maaster to the next

  horner_cubic_stage_fsm #(
      .MULT (A),
      .CONST(B)
  ) ab (
      .rst,
      .clk,
      .previ(abtbi),
      .prevo(abtbo),
      .nexto(abbco_bcabi),  //master
      .nexti(abbci_bcabo)
  );
  horner_cubic_stage_fsm #(
      .MULT (1.0),
      .CONST(C)
  ) bc (
      .clk,
      .rst,
      .previ(abbco_bcabi),  // slave
      .prevo(abbci_bcabo),
      .nexti(bccdi_cdbco),  // master
      .nexto(bccdo_cdbci)
  );
  horner_cubic_stage_fsm #(
      .MULT (1.0),
      .CONST(D)
  ) cd (
      .clk,
      .rst,
      .previ(bccdo_cdbci),  //slave
      .prevo(bccdi_cdbco),  //all ports naming conv: thisview
      .nexti(cdtbi),
      .nexto(cdtbo)
  );

endmodule

`endif
