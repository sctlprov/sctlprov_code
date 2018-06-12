all:
	make -C src all
	mv src/sctl sctl 

testing:
	make -C src testing
	mv src/testing testing

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