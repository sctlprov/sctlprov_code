# 1 Introduction

The `benchmarks` folder contains CTL benchmark files for model checker [Verds](http://lcs.ios.ac.cn/~zwh/verds/index.html), [NuSMV](http://nusmv.fbk.eu/), [NuXMV](https://nuxmv.fbk.eu/), theorem prover [iProver Modulo](http://www.ensiie.fr/~guillaume.burel/blackandwhite_iProverModulo.html.en), and our tool [SCTLProV](https://github.com/terminatorlxj/SCTLProV). The benchmarks consists of two set of programs: randomly generated boolean program, and fairness programs.

## 1.1 Randomly generated programs
Benchmark #1, #2, and #3 are all randomly generated programs. 

- The original description of benchmark #1 is in the website of model checker [Verds](http://lcs.ios.ac.cn/~zwh/verds/verds_pdf/verds1.30eeq.pdf) and also restated in the file `description.md` of the folder `random_programs`.
- Based on benchmark #1, we extend the number of variables to tens, hundreds, and even thousands in benchmark #2 and #3.
- For benchmark #3, the input files for iProver Modulo is not presented here. It is due to the fact that these input files are too large to upload (more than 26GB in total). However, thanks to Kailiang Ji (the author of the paper "CTL Model Checking in Deduction Modulo" that describe the use of iProver Modulo in CTL model checking), interested readers may refer to this little [converting tool](https://github.com/kailiangji/SMV2TPTP) that can convert `.smv` files into `.p` files for iProver Modulo.


The randomness of the test cases in three benchmarks makes it rather fair for different CTL model checking approaches, and helps us recognize the strengths and weaknesses of each tool. 

## 1.2 Fairness programs

Benchmark #4 is also based on a [benchmark](http://lcs.ios.ac.cn/~zwh/verds/verds_code/bp12.rar) on the Verds website. We added input files for SCTLProV in benchmark #4.
Benchmark #4 consists of two sets of concurrent programs: the mutual exclusion algorithms and the ring algorithms. The description of the fairness programs are in the file `description.md` of the folder `fairness_programs`.

Both kinds of algorithms consist of a set of concurrent processes running in parallel, and some formulae to be verified. Each formula in the algorithms needs to be verified under the fairness constraint that each process does not starve, i.e., no process waits infinitely often.

# 2 Program generators

### 2.1 Randomly generated progrems

The OCaml programs to generate the randomly programs are in the folder `random_programs_generator`:

1. `generator_p1.ml`: for concurrent processes;
2. `generator_p2.ml`: for concurrent sequential processes.

### 2.2 Fairness programs

The OCaml programs to generate the fairness programs are in folder `fairness_programs_generator`:

1. `generate_mutual.ml`: for mutual exclusion algorithms;
2. `generate_ring.ml`: for ring algorithms.

# 3 Run these examples

## 3.1 Run test cases one-by-one

- Files with `.vvm` in the extension is in the input format 
  of the model verifier verds. Run these examples using command

  	verds -QBF \<filename\> 

- Files with `.smv` in the extension is in the input format of the model verifier NuSMV and NuXMV. Run these examples using command

   NuSMV -dcx \<filename\>
   or

   	NuXMV -dcx \<filename\>

- Files with `.model` in the extension is in the input format of the model verifier SCTLProV. Run these examples using command

   sctl \<filename\>
   or

   	sctl -bdd \<filename\>

- Files with `.p` in the extension is in the input format of the theorem prover iProver Modulo. Run these examples using command

   iproveropt  \`cat basic_resolution_options\`  --modulo true --res_passive_queue_flag false --res_lit_sel ctl_sel  \<filename\>


## 3.2 Running script 

As there are so many test cases in each benchmark, we wrote a script (also in OCaml) that can run many test cases and generated the results at once. The script is in the folder `generate_result_script`.

**Compile the script:** 

1. Change `generate_result_script` as the working directory;
2. `Make` or `Make all`;
3. The executable file `run` is generated.

**Usage of the executable file`run`:**

   `run -exec <command> -timeout <tmot> -dir <targetdir> -surfix <sfx> [-extra <filename>]`

   Each argument of the command is explained as follows:

 1.  `-exec <command>`:  This argument specifies the provers or model checker to run, where `command` is the **absolute** file path of the executable of the provers or model checker, for instance `-exec /home/jian/SCTLProV/sctl`;

 2.  `-timeout <tmot>`:  This argument specifies the limit of the running time of the provers or model checkers, where `tmot` is the amout of time, the format of `tmot` is the same as in the linux shell. For instance, `-timeout 20m` specifies the limit of running time is 20 minutes;

 3.  `-dir <targetdir>`: This argument specifies the target directory where the files of test cases is. `targetdir` is the **absolute** file path of the target dir, for instance:

     `-dir /home/jian/benchmark1/p1/p01/sctl/`

 4. `-surfix <sfx>`: This argument specifies the surfix of each test cases. For instance, the surfix of test cases for SCTLProV is "model", which can be specifies as `-surfix model`.

 5. `-extra <filename>`: This argument is optional, which specifies the extra arguments of the provers or model checkers. Extra arguments are in the file `filename` which is in text format. For instance, to evaluate test cases in NuSMV, the extra argument `-dcx` is specifies in order to improve efficiency. In this case, we put `-dcx` as the first line in the file `nusmv_extra`, and when running NuSMV using the script, we use `-extra nusmv_extra` as an argument of the script. 

**Complete examples：**

- SCTLProV: 

  `run -exec /home/jian/SCTLProV/sctl -timeout 20m -dir /home/jian/benchmark1/p1/p01/sctl/ -surfix model `

- Verds:

  `run -exec /home/jian/verds/verds -timeout 20m -dir /home/jian/benchmark1/p1/p01/verds/ -surfix vvm -extra verds_extra`

- iProver Modulo:

  `run -exec /home/jian/iprover/iproveropt -timeout 20m -dir /home/jian/benchmark1/p1/p01/iprover/ -surfix p -extra iprover_extra`

- NuSMV/NuXMV:

  `run -exec /home/jian/nusmv/bin/NuSMV -timeout 20m -dir /home/jian/benchmark1/p1/p01/smv/ -surfix smv -extra nusmv_extra`

**Result:**

The experimental results is in the auto-generated file `result_<timestamp>` and `result_<timestamp>_data`.

**Note:**

Inside the script, `/usr/bin/time -v` is used to generate the time and memory usage for each test cases. For test cases where more accurate time usage is needed, please use `time` instead of `/usr/bin/time`.
