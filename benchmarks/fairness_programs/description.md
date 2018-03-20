The files are named `X_aABC.vvm`, `X_aABC.smv`, and `X_aABC.model`
which are supposed to to represent the same verication problem for 
a given `X_aABC` in a subdirectory.

## FILES in folder mutual (mutual exclusion algorithm) not satisfying the good properties:


The meaning of ABC is as follows.
AB+1   	is the number of the processes in the model;
C    	is the number of the property in the model;

## FILES in folder ring (ring processes):

The meaning of ABC is as follows.

AB   	is the number of the processes in the model;
C    	is the number of the property in the model;

## Run these examples

- Files with `.vvm` in the extension is in the input format 
of the model verifier verds. Run these examples using command

		verds -QBF <filename> 
	
- Files with `.smv` in the extension is in the input format of the model verifier NuSMV and NuXMV. Run these examples using command

		NuSMV -dcx <filename>
or

		NuXMV -dcx <filename>
	
- Files with `.model` in the extension is in the input format of the model verifier SCTLProV. Run these examples using command

		sctl <filename>
or
		
		sctl -bdd <filename>
