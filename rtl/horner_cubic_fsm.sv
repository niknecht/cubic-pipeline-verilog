`timescale 1ns / 1ps

`include "axi_stream_if.sv"

module horner_cubic_stage_fsm #(
    parameter signed [31:0] MULT,  // ISO 754 floating point
    parameter signed [31:0] CONST
) (
    input rst,
    clk,
    axi_stream_if.slave prev,  // Slave to the previous
    axi_stream_if.master next  // Maaster to the next
);
  var real mult = real'(MULT);  // reinterpret_cast
  var real c = real'(CONST);
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
      IDLE: if (prev.cb_slave.TVALID) next_state = LOAD;
      LOAD: next_state = RES;
      RES:  if (next.cb_master.TREADY) next_state = IDLE;
    endcase
  end

  always_ff @(posedge clk) begin  // Update state
    if (rst) state <= IDLE;
    else state <= next_state;
  end


  // Datapath
  // Output evaluation
  always_comb begin
    data = data;
    if ((state == IDLE) && prev.cb_slave.TVALID) data = prev.cb_slave.TDATA;
  end
  always_comb begin
    res = res;
    if (state == LOAD) res = data * mult + c;
  end
  // Output propagation
  always_ff @(prev.cb_slave) begin  // Ready in wait, otherwise not
    prev.cb_slave.TREADY <= (state == IDLE);
  end
  always_ff @(next.cb_master) begin  // Result accumulation here, if ready
    next.cb_master.TVALID <= (state == RES);
    next.cb_master.TDATA  <= (state == RES) ? res : 0;
    next.cb_master.TLAST  <= '0;
  end
endmodule

// Assembling the pipeline
module horner_cubic_fsm #(
    parameter signed [31:0] A,
    parameter signed [31:0] B,
    parameter signed [31:0] C,
    parameter signed [31:0] D
) (
    input clk,
    rst,
    axi_stream_if.slave tbab_in,
    axi_stream_if.master cdtb_out
);
  axi_stream_if abbc_if (
      .clk,
      .rst
  );
  axi_stream_if bccd_if (
      .rst,
      .clk
  );

  horner_cubic_stage_fsm #(
      .MULT (A),
      .CONST(B)
  ) ab (
      .rst,
      .clk,
      .prev(tbab_in),
      .next(abbc_if.master)
  );
  horner_cubic_stage_fsm #(
      .MULT (1.0),
      .CONST(C)
  ) bc (
      .clk,
      .rst,
      .prev(abbc_if.slave),
      .next(bccd_if.master)
  );
  horner_cubic_stage_fsm #(
      .MULT (1.0),
      .CONST(D)
  ) cd (
      .clk,
      .rst,
      .prev(bccd_if.slave),
      .next(cdtb_out)
  );

endmodule
