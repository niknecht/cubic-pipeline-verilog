`include "rtl/horner_cubic_fsm.sv"

`timescale 1ns / 1ps

`ifndef TEST_A
`define TEST_A 1.0
`endif
`ifndef TEST_B
`define TEST_B 2.0
`endif
`ifndef TEST_C
`define TEST_C 3.5
`endif
`ifndef TEST_D
`define TEST_D 4.5
`endif
`ifndef X_VALS
`define X_VALS '{2.0, 1.0, 10.0, -1.0}
`endif

module tb_top;
  logic clk = 0, rst = 0;
  axi_stream_masteri_slaveo_t tbabi;  // Master, slave is reversed
  axi_stream_mastero_slavei_t tbabo;
  axi_stream_masteri_slaveo_t tbcdo;
  axi_stream_mastero_slavei_t tbcdi;

  horner_cubic_fsm #(
      .A(`TEST_A),  // Defined in a compiler directive
      .B(`TEST_B),
      .C(`TEST_C),
      .D(`TEST_D)
  ) dut (
      .clk,
      .rst,
      .abtbi(tbabo),
      .abtbo(tbabi),
      .cdtbo(tbcdi),
      .cdtbi(tbcdo)
  );
  initial begin
    tbcdo.TREADY = 1'b1;  // Always ready to receive
  end

  always @(posedge clk) begin
    if (rst) begin
      tbcdo.TREADY <= 1'b0;
    end else tbcdo.TREADY <= 1'b1;
  end

  always #5 clk = ~clk;

  initial begin
    rst = 1;
    repeat (10) @(posedge clk);
    rst = 0;
  end

  real x_tests[] = `X_VALS;
  initial begin
    wait (!rst);
    @(posedge clk);
    $display("Beginning  tests");
    for (int test_i = 0; test_i < x_tests.size(); test_i++) begin
      //foreach (x_tests[i]) begin  // No support? <:(
      $display("Testing x=%f", x_tests[test_i]);
      drive_x(x_tests[test_i]);
      check_result(x_tests[test_i]);
      short_reset();
    end
    $display("All tests complete");
    $finish;
  end

  task automatic check_result(real x);
    real trueVal = `TEST_A * x * x * x + `TEST_B * x * x + `TEST_C * x + `TEST_D;
    @(posedge clk) begin
      if (rst) tbcdo.TREADY <= '0;
      else tbcdo.TREADY <= '1;
    end
    wait (tbcdi.TVALID && tbcdo.TREADY && tbcdi.TLAST)
      if (!(($bitstoreal(
              tbcdi.TDATA
          ) >= trueVal * 0.999) && ($bitstoreal(
              tbcdi.TDATA
          ) <= trueVal * 1.001)))  //inside {[trueVal * 0.999 : trueVal * 1.001]}))
        // Not all compilers support tolerances, sadly
        $error(
            "Test for {A=%f, B=%f, C=%f, D=%f, x=%f}: FAILURE\nYour value: %f, trueVal: %f",
            `TEST_A,
            `TEST_B,
            `TEST_C,
            `TEST_D,
            x,
            $bitstoreal(
                tbcdi.TDATA
            ),
            trueVal
        );
      else
        $display(
            "Test for {A=%f, B=%f, C=%f, D=%f, x=%f}: success",
            `TEST_A,
            `TEST_B,
            `TEST_C,
            `TEST_D,
            x
        );
  endtask

  task automatic drive_x(real x);
    tbabo.TVALID = 1;
    tbabo.TLAST  = 1;
    tbabo.TDATA  = $realtobits(x);
    $display("In drive_x translating TDATA before handshake: %f", $bitstoreal(tbabo.TDATA));
    @(posedge clk);

    /*do begin
      @(posedge clk);
      $display("TIME %0t: TVALID=%0b TREADY=%0b", $time, tbabo.TVALID, tbabi.TREADY);
      if ($time > 1000) $fatal(1, "Backpressure is held too long");  // Tb msater timeout
    end while (!tbabi.TREADY);*/

    @(posedge clk);
    while (!(tbabo.TVALID && tbabi.TREADY)) @(posedge clk);

    $display("In drive_x translating TDATA after handshake: %f", $bitstoreal(tbabo.TDATA));

    tbabo.TVALID = 0;
    tbabo.TLAST  = 0;
    @(posedge clk);
  endtask
  /*   tbabo.TDATA  <= $realtobits(x);
    tbabo.TVALID <= '1;
    tbabo.TLAST  <= '1;
    wait (tbabi.TREADY) @(posedge clk) tbabo.TVALID <= '0;
  endtask*/

  task automatic short_reset();
    repeat (5) @(posedge clk);
  endtask

  always @(posedge clk) begin
    if (!rst) begin
      $monitor("T%0t TB->STAGE TVALID:%b, TREADY:%b, TLAST:%b, TDATA:%b", $time, tbabo.TVALID,
               tbabi.TREADY, tbabo.TLAST, tbabo.TDATA);
      $monitor("T%0t STAGE->TB TVALID:%b, TREADY:%b, TLAST:%b, TDATA:%b", $time, tbcdi.TVALID,
               tbcdo.TREADY, tbcdi.TLAST, tbcdi.TDATA);
    end
  end

endmodule

