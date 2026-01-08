target simv: tb/tb_top.sv rtl/*.sv
	iverilog -g2012 -s tb_top tb/tb_top.sv rtl/*.sv -o simv \
  -DTEST_A=$(TEST_A) -DTEST_B=$(TEST_B) -DTEST_C=$(TEST_C) -DTEST_D=$(TEST_D) \
  -DTEST_VALS="$(TEST_VALS)"

.PHONY: clean
clean:

