make TEST_A=1.0 TEST_B=2.0 TEST_C=3.5 TEST_D=4.5 TEST_VALS="{1.0, 0.0, -1.0, 10.0}"
vvp simv
make clean
make TEST_A=2.0 TEST_B=1.0 TEST_C=0.0 TEST_D=-1.0 TEST_VALS="{1.0, 0.0, 2.0, -1.0}"
vvp simv
make clean
make TEST_A=0.0 TEST_B=10.0 TEST_C=0.5 TEST_D=-2.0 TEST_VALS="{10.0, 0.5, 100.0, 1.0e-3}"
vvp simv
make clean
make TEST_A=100.0 TEST_B=-10.0 TEST_C=1.0e-3 TEST_D=1.0e6 TEST_VALS="{-10.0, 2.0, 5.0, 1.0e-3}"
vvp simv
make clean
