# -------------------------------------------------------------------------- #
#                                                                            #
#  A verified resolution checker written in SPARK 2014 based on functional   #
#  data structures.                                                          #
#                                                                            #
# -------------------------------------------------------------------------- #
#                                                                            #
#  Copyright (C) 2021, Tobias Philipp                                        #
#                                                                            #
# -------------------------------------------------------------------------- #

CORES=2



build:
	gprbuild -Pchecker -p -we -Xver=debug
	gprbuild -Ptest

test:
	gprbuild -Ptest -p -we -bargs -Es
	bin/test

release:
	gprbuild -Pchecker -p -we -Xver=release
	strip --strip-all bin/release/checker

release_win:
	gprbuild -Pchecker -p -we -Xver=release --target=x86_64-windows

clean:
	gprclean -Pchecker
	gprclean -Ptest
	rm -rf obj
	rm -rf bin

proof: build
	gnatprove -Pchecker -Xver=release --timeout=15 -j$(CORES) --level=4 --proof=progressive --prover=z3,cvc4,altergo


.PHONY: clean build proof release release_win
