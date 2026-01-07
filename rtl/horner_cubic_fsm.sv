`ifndef HORNER_CUBIC_FSM_SV
`define HORNER_CUBIC_FSM_SV

`timescale 1ns / 1ps

`include "rtl/axi_stream_if.sv"

module horner_cubic_stage_fsm #(
    parameter real CONST
) (
    input rst,
    clk,
    input real x,
    input axi_stream_mastero_slavei_t previ,  // Slave to the previous
    output axi_stream_masteri_slaveo_t prevo,
    input axi_stream_masteri_slaveo_t nexti,
    output axi_stream_mastero_slavei_t nexto  // Maaster to the next
);
  reg [63:0] data_bits;
  reg [63:0] res_bits;
  logic data_valid;

  always_ff @(posedge clk) begin
    if (rst) begin
      data_bits  <= 0;
      data_valid <= 0;
    end else if (previ.TVALID && prevo.TREADY) begin
      data_bits  <= previ.TDATA;
      data_valid <= previ.TVALID;
      $display("TDATA in stages: %f", $bitstoreal(previ.TDATA));
    end
  end

  // Moore FSM for protocol
  typedef enum logic [1:0] {
    IDLE = 2'b00,
    LOAD = 2'b01,
    RES  = 2'b10
  } state_t;

  state_t state, next_state;

  always @(*) begin
    next_state = state;
    case (state)
      IDLE: if (previ.TVALID) next_state = LOAD;
      LOAD: next_state = RES;
      RES: if (nexti.TREADY) next_state = IDLE;
      default: next_state = IDLE;
    endcase
  end

  always_ff @(posedge clk) begin  // Update state
    if (rst) state <= IDLE;
    else state <= next_state;
  end


  // Datapath
  // Output evaluation
  always_ff @(posedge clk) begin
    if (rst) res_bits <= 0;
    else if (state == LOAD && data_valid) begin
      res_bits <= $realtobits($bitstoreal(data_bits) * x + CONST);
      //$display("Computed %f * %f + %f as %f", $bitstoreal(data_bits), MULT, CONST, $bitstoreal(
      //                                                                  res_bits));
    end
  end
  /*always @(*) begin // old
    if (rst) res = 0;
    else if (state == LOAD) begin
      res = $bitstoreal(data_bits) * MULT + CONST;
      $display("Computed %f * %f + %f as %f", $bitstoreal(data_bits), MULT, CONST, res);
    end
  end*/  // old
  // Output propagation
  always_ff @(posedge clk) begin
    if (rst) begin
      prevo.TREADY <= 0;

      nexto.TVALID <= 0;
      nexto.TDATA  <= 0.0;
      nexto.TLAST  <= 0;
    end else begin
      prevo.TREADY <= (state == IDLE);

      nexto.TVALID <= (state == RES);
      //if (nexto.TVALID) begin
      nexto.TDATA  <= res_bits;
      $display("Computed %f * %f + %f as %f", $bitstoreal(data_bits), x, CONST, $bitstoreal(
                                                                                    res_bits));
      //end
      nexto.TLAST <= (state == RES);
    end
    // Next has cb_master, prev has cb_slave, removed for verilator compatibility
  end

  //=============================================================================================================
  //-------------------------------------------------------------------------------------------------------------

  always @(posedge clk)
    if (!rst)
      $monitor(
          "T%0t, STAGE:%d->NEXT:%d, TVALID:%b, TDATA:%b, TLAST:%b, TREADY:%b",
          $time,
          state,
          next_state,
          nexto.TVALID,
          nexto.TDATA,
          nexto.TLAST,
          nexti.TREADY
      );

  reg tv_valid_d;
  always @(posedge clk)
    if (rst) tv_valid_d <= 0;
    else tv_valid_d <= nexto.TVALID;
  always @(posedge clk) begin
    if (!rst && nexto.TVALID && !nexti.TREADY) begin
      if (!tv_valid_d) begin
        $error("TVALID dropped before handshake");
        $finish;
      end
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
        $finish;
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
        if (tdata_d !== nexto.TDATA) begin
          $error("TDATA changed during backpressure");
          $finish;
        end
        if (tlast_d !== nexto.TLAST) begin
          $error("TLAST changed during backpressure");
          $finish;
        end
      end
    end
  end

  // valid_on_last, on of the two slave-side checks
  always @(posedge clk) begin
    if (!rst && previ.TLAST && !previ.TVALID) begin
      $error("TLAST without TVALID at %0t", $time);
      $finish;
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
    input real x,
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
      .CONST(B)
  ) ab (
      .rst,
      .clk,
      .x,
      .previ(abtbi),
      .prevo(abtbo),
      .nexto(abbco_bcabi),  //master
      .nexti(abbci_bcabo)
  );
  horner_cubic_stage_fsm #(
      .CONST(C)
  ) bc (
      .clk,
      .rst,
      .x,
      .previ(abbco_bcabi),  // slave
      .prevo(abbci_bcabo),
      .nexti(bccdi_cdbco),  // master
      .nexto(bccdo_cdbci)
  );
  horner_cubic_stage_fsm #(
      .CONST(D)
  ) cd (
      .clk,
      .rst,
      .x,
      .previ(bccdo_cdbci),  //slave
      .prevo(bccdi_cdbco),  //all ports naming conv: thisview
      .nexti(cdtbi),
      .nexto(cdtbo)
  );

endmodule

`endif
