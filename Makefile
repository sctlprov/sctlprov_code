all:
	make -C src all
	mv src/sctl sctl 

opt:
	make -C src/opt all
	mv src/opt/sctl sctl

bcg:
	make -C src/bcg all
	mv src/bcg/sctl sctl

clean:
	make -C src clean
	rm -f sctl
	rm -f testing
	rm -f *.log
	rm -f *.cache