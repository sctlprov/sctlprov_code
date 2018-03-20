## FILES in p1/random boolean concurrent programs:
----

The files are named ABCDEF.p (for iprover), ABCDEF.model (for SCTLProV), ABCDEF.vvm (for Verds) and ABCDEF.smv (for NuSMV and NuXMV)
which are supposed to represent the same verication problem for 
a given ABCDEF in this subdirectory.


The meaning of the string ABCDEF in the file name in p1 is as follows.

- AB   is the number of the property in the model;
- CD*6 is the number of boolean variables in the model;
- EF   is the sequence number of the randomly generated program;


## FILES in p2/random boolean concurrent sequential programs:
----

The files are named ABCDEF.p (for iprover), ABCDEF.model (for SCTLProV), ABCDEF.vvm (for Verds) and ABCDEF.smv (for NuSMV and NuXMV)
which are supposed to represent the same verication problem for 
a given ABCDEF in this subdirectory.

The meaning of the string ABCDEF in the file name in p2 is as follows.

- AB   is the number of the property in the model;
- CD*4 is the number of boolean variables in the model;
- EF   is the sequence number of the randomly generated program;

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

- Files with `.p` in the extension is in the input format of the theorem prover iProver Modulo. Run these examples using command

		iproveropt  `cat basic_resolution_options`  --modulo true --res_passive_queue_flag false --res_lit_sel ctl_sel  <filename>