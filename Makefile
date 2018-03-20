all:
	make -C src all
	mv src/sctl sctl 

clean:
	make -C src clean
	rm -f sctl