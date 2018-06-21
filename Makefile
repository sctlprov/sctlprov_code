all:
	make -C src all
	mv src/sctl sctl 

finite:
	make -C src/finite all
	mv src/finite/sctl sctl

bcg:
	make -C src/bcg all
	mv src/bcg/sctl sctl

no-bcg:
	make -C src no-bcg
	mv src/sctl sctl

clean:
	make -C src clean
	rm -f sctl
	rm -f testing
	rm -f *.log
	rm -f *.cache